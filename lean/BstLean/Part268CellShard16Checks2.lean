import BstLean.Part268CellShard16Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12750_40 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (16539192586489 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449107054737 / 20000000000000 : ℝ))
      (E := (cell12750 ⟨40, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (16539192586489 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449107054737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_41 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (82661973713687 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449107861939 / 20000000000000 : ℝ))
      (E := (cell12750 ⟨41, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (82661973713687 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449107861939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_42 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20657002021707 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (561385833099 / 25000000000000 : ℝ))
      (E := (cell12750 ⟨42, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20657002021707 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (561385833099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_43 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20648516505553 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122773670441 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨43, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20648516505553 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122773670441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_44 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (2580004609073 / 3125000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245551334027 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨44, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (2580004609073 / 3125000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245551334027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_45 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (16505250492369 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (224555531049 / 10000000000000 : ℝ))
      (E := (cell12750 ⟨45, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (16505250492369 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (224555531049 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_46 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (8249238090753 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449111865521 / 20000000000000 : ℝ))
      (E := (cell12750 ⟨46, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (8249238090753 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449111865521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_47 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (8245853279833 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245563324753 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨47, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (8245853279833 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245563324753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_48 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (82424708105331 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (561391839721 / 25000000000000 : ℝ))
      (E := (cell12750 ⟨48, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (82424708105331 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (561391839721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_49 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41195453399881 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449114273781 / 20000000000000 : ℝ))
      (E := (cell12750 ⟨49, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41195453399881 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (449114273781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_50 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41178564426499 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245575352399 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨50, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41178564426499 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245575352399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_51 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20580843559139 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245579365751 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨51, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20580843559139 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245579365751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_52 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (5143102682631 / 6250000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122791673579 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨52, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (5143102682631 / 6250000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122791673579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_53 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (82255934881419 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (224558735263 / 10000000000000 : ℝ))
      (E := (cell12750 ⟨53, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (82255934881419 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (224558735263 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_54 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (8222225008647 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245591378977 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨54, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (8222225008647 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245591378977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_55 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (8218858850933 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245595363697 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨55, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (8218858850933 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245595363697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_56 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41077475061111 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (224559942137 / 10000000000000 : ℝ))
      (E := (cell12750 ⟨56, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41077475061111 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (224559942137 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_57 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (82121334897507 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (44912068599 / 2000000000000 : ℝ))
      (E := (cell12750 ⟨57, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (82121334897507 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (44912068599 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_58 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41043871403841 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122803692673 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨58, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41043871403841 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122803692673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_59 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (10256771728173 / 12500000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122805700829 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨59, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (10256771728173 / 12500000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122805700829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12751_40 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (16539192061161 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245414241073 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨40, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (16539192061161 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245414241073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_41 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (2066549284697 / 2500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245418274381 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨41, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (2066549284697 / 2500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245418274381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_42 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41314003030719 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (140338889767 / 6250000000000 : ℝ))
      (E := (cell12751 ⟨42, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41314003030719 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (140338889767 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_43 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41297032148413 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245426243413 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨43, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41297032148413 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245426243413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_44 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (4128007303227 / 5000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (8981721179 / 400000000000 : ℝ))
      (E := (cell12751 ⟨44, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (4128007303227 / 5000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (8981721179 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_45 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41263125667613 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224543427127 / 10000000000000 : ℝ))
      (E := (cell12751 ⟨45, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41263125667613 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224543427127 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_46 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82492380079677 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224543828913 / 10000000000000 : ℝ))
      (E := (cell12751 ⟨46, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82492380079677 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224543828913 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_47 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (2576829133401 / 3125000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224544228771 / 10000000000000 : ℝ))
      (E := (cell12751 ⟨47, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (2576829133401 / 3125000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224544228771 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_48 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82424707873777 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245446265021 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨48, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82424707873777 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245446265021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_49 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41195453432871 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245450277823 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨49, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41195453432871 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245450277823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_50 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82357129216103 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561363580943 / 25000000000000 : ℝ))
      (E := (cell12751 ⟨50, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82357129216103 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561363580943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_51 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82323374896377 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245458282289 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨51, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82323374896377 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245458282289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_52 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82289643878227 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122731163783 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨52, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82289643878227 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122731163783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_53 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82255936133453 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (112273316929 / 5000000000000 : ℝ))
      (E := (cell12751 ⟨53, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82255936133453 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (112273316929 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_54 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (82222251633999 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245470312071 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨54, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (82222251633999 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245470312071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_55 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (1643771807039 / 2000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (112273718139 / 5000000000000 : ℝ))
      (E := (cell12751 ⟨55, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (1643771807039 / 2000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (112273718139 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_56 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (10269369032441 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245478368913 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨56, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (10269369032441 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245478368913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_57 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41060668664547 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245482326587 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨57, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41060668664547 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245482326587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_58 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (20521936383287 / 25000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (112274317503 / 5000000000000 : ℝ))
      (E := (cell12751 ⟨58, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (20521936383287 / 25000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (112274317503 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_59 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (3282167073773 / 4000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122745187989 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨59, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (3282167073773 / 4000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122745187989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12752_40 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (10336994710003 / 12500000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (449058641067 / 20000000000000 : ℝ))
      (E := (cell12752 ⟨40, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (10336994710003 / 12500000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (449058641067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_41 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (5166373066431 / 6250000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245297235977 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨41, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (5166373066431 / 6250000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245297235977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_42 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (20657001009209 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245301254693 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨42, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (20657001009209 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245301254693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_43 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82594062572191 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122652630287 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨43, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82594062572191 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122652630287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_44 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82560144639459 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122654626247 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨44, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82560144639459 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122654626247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_45 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82526250209287 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245313229107 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨45, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82526250209287 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245313229107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_46 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82492379252467 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (8981268991 / 400000000000 : ℝ))
      (E := (cell12752 ⟨46, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82492379252467 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (8981268991 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_47 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (4122926586997 / 5000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (11226606239 / 500000000000 : ℝ))
      (E := (cell12752 ⟨47, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (4122926586997 / 5000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (11226606239 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_48 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82424707642793 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245325286207 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨48, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82424707642793 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245325286207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_49 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82390906932257 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122664650937 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨49, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82390906932257 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122664650937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_50 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82357129579707 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245333292387 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨50, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82357129579707 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245333292387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_51 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41161687778331 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245337314127 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨51, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41161687778331 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245337314127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_52 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (16457928966957 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245341305289 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨52, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (16457928966957 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245341305289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_53 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82255937385877 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245345321883 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨53, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82255937385877 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245345321883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_54 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (16444450636377 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122674650817 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨54, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (16444450636377 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122674650817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_55 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (8218859219489 / 10000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122676650091 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨55, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (8218859219489 / 10000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122676650091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_56 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82154954397119 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (561339328479 / 25000000000000 : ℝ))
      (E := (cell12752 ⟨56, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82154954397119 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (561339328479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_57 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (82121339760931 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (89814453561 / 4000000000000 : ℝ))
      (E := (cell12752 ⟨57, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (82121339760931 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (89814453561 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_58 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (20521937064707 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245365312307 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨58, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (20521937064707 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245365312307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_59 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (16410835972689 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122684673933 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨59, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (16410835972689 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122684673933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12753_40 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (82695955055103 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122586112611 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨40, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (82695955055103 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122586112611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_41 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (16532393347747 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (112258812663 / 5000000000000 : ℝ))
      (E := (cell12753 ⟨41, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (16532393347747 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (112258812663 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_42 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (4131400100651 / 5000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122590135031 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨42, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (4131400100651 / 5000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122590135031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_43 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41297030424153 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (14032401717 / 625000000000 : ℝ))
      (E := (cell12753 ⟨43, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41297030424153 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (14032401717 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_44 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (20640035803773 / 25000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449037653221 / 20000000000000 : ℝ))
      (E := (cell12753 ⟨44, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (20640035803773 / 25000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449037653221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_45 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (3301049963361 / 4000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122596121437 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨45, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (3301049963361 / 4000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122596121437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_46 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (82492378425899 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122598131179 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨46, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (82492378425899 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122598131179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_47 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41229265605827 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122600131969 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨47, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41229265605827 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122600131969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_48 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (82424707412379 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122602152281 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨48, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (82424707412379 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122602152281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_49 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (16478181399861 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561302080783 / 25000000000000 : ℝ))
      (E := (cell12753 ⟨49, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (16478181399861 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561302080783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_50 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (82357129943809 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (140325769827 / 6250000000000 : ℝ))
      (E := (cell12753 ⟨50, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (82357129943809 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (140325769827 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_51 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (8232337621741 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280652035529 / 12500000000000 : ℝ))
      (E := (cell12753 ⟨51, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (8232337621741 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280652035529 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_52 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (8228964579177 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122610169681 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨52, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (8228964579177 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122610169681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_53 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41127969319347 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280653037817 / 12500000000000 : ℝ))
      (E := (cell12753 ⟨53, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41127969319347 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280653037817 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_54 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41111127365063 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561307086917 / 25000000000000 : ℝ))
      (E := (cell12753 ⟨54, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41111127365063 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561307086917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_55 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (82188594038151 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245232353219 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨55, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (82188594038151 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245232353219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_56 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41077478267497 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (224523631551 / 10000000000000 : ℝ))
      (E := (cell12753 ⟨56, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41077478267497 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (224523631551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_57 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (82121342193017 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (14032752181 / 625000000000 : ℝ))
      (E := (cell12753 ⟨57, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (82121342193017 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (14032752181 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_58 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (82087750984721 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449048866253 / 20000000000000 : ℝ))
      (E := (cell12753 ⟨58, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (82087750984721 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449048866253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_59 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (10256772860343 / 12500000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561312094131 / 25000000000000 : ℝ))
      (E := (cell12753 ⟨59, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (10256772860343 / 12500000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561312094131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12754_40 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (82695952431041 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (17539463287 / 781250000000 : ℝ))
      (E := (cell12754 ⟨40, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (82695952431041 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (17539463287 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_41 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (82661964415397 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122527633727 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨41, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (82661964415397 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122527633727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_42 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (8262799998999 / 10000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245059282381 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨42, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (8262799998999 / 10000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245059282381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_43 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (20648514781293 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561265821463 / 25000000000000 : ℝ))
      (E := (cell12754 ⟨43, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (20648514781293 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561265821463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_44 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (1032001772393 / 1250000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122533667793 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨44, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (1032001772393 / 1250000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122533667793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_45 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41263123979721 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (224507131257 / 10000000000000 : ℝ))
      (E := (cell12754 ⟨45, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41263123979721 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (224507131257 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_46 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (82492377599973 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122537666479 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨46, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (82492377599973 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122537666479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_47 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (3298341227359 / 4000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (35079364627 / 1562500000000 : ℝ))
      (E := (cell12754 ⟨47, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (3298341227359 / 4000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (35079364627 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_48 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (10303088397817 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245083320087 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨48, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (10303088397817 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245083320087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_49 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (10298863383361 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245087341597 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨49, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (10298863383361 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245087341597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_50 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (82357130308409 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122545669661 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨50, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (82357130308409 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122545669661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_51 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (4116168843931 / 5000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245095369641 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨51, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (4116168843931 / 5000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245095369641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_52 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41144823374591 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (8769919417 / 390625000000 : ℝ))
      (E := (cell12754 ⟨52, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41144823374591 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (8769919417 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_53 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (82255939891901 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122551669801 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨53, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (82255939891901 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122551669801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_54 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41111128139361 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245107391093 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨54, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41111128139361 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245107391093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_55 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (20547148970433 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245111403683 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨55, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (20547148970433 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245111403683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_56 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41077479336577 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (449023074739 / 20000000000000 : ℝ))
      (E := (cell12754 ⟨56, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41077479336577 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (449023074739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_57 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (10265168078169 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245119415547 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨57, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (10265168078169 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245119415547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_58 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (20521938427707 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245123406933 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨58, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (20521938427707 / 25000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2245123406933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_59 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (4102709295111 / 5000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122563701377 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨59, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (4102709295111 / 5000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122563701377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12755_40 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82695949807837 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122465186563 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨40, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82695949807837 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122465186563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_41 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82661962092881 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244934396113 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨41, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82661962092881 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244934396113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_42 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82627997967747 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (140308646903 / 6250000000000 : ℝ))
      (E := (cell12755 ⟨42, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82627997967747 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (140308646903 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_43 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82594057402787 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (70154450363 / 3125000000000 : ℝ))
      (E := (cell12755 ⟨43, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82594057402787 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (70154450363 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_44 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82560140368501 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244946402091 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨44, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82560140368501 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244946402091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_45 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (5157890427221 / 6250000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244950379327 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨45, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (5157890427221 / 6250000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244950379327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_46 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (2577886774209 / 3125000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (448990880131 / 20000000000000 : ℝ))
      (E := (cell12755 ⟨46, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (2577886774209 / 3125000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (448990880131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_47 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82458530156901 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244958405451 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨47, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82458530156901 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244958405451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_48 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (41212353476631 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (89798495669 / 4000000000000 : ℝ))
      (E := (cell12755 ⟨48, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (41212353476631 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (89798495669 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_49 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (16478181427001 / 20000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244966416233 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨49, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (16478181427001 / 20000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244966416233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_50 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (20589282668377 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122485208821 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨50, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (20589282668377 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122485208821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_51 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (20580844385073 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244974452331 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨51, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (20580844385073 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244974452331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_52 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82289647707021 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122489229247 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨52, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82289647707021 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122489229247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_53 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82255941145499 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (56124560827 / 2500000000000 : ℝ))
      (E := (cell12755 ⟨53, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82255941145499 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (56124560827 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_54 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (41111128913837 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244986431907 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨54, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (41111128913837 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244986431907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_55 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (1284196839463 / 1562500000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122495225787 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨55, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (1284196839463 / 1562500000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122495225787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_56 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (41077480405799 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (280624311059 / 12500000000000 : ℝ))
      (E := (cell12755 ⟨56, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (41077480405799 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (280624311059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_57 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (5132584191121 / 6250000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244998479633 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨57, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (5132584191121 / 6250000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244998479633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_58 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (82087756437149 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2245002480137 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨58, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (82087756437149 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2245002480137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_59 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (5251468091 / 6400000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (449001297151 / 20000000000000 : ℝ))
      (E := (cell12755 ⟨59, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (5251468091 / 6400000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (449001297151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12756_40 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (20673986796373 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448961900229 / 20000000000000 : ℝ))
      (E := (cell12756 ⟨40, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (20673986796373 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448961900229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_41 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82661959771187 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (224481346291 / 10000000000000 : ℝ))
      (E := (cell12756 ⟨41, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82661959771187 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (224481346291 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_42 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (8262799594629 / 10000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448963494853 / 20000000000000 : ℝ))
      (E := (cell12756 ⟨42, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (8262799594629 / 10000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448963494853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_43 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (645266060009 / 781250000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448964295109 / 20000000000000 : ℝ))
      (E := (cell12756 ⟨43, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (645266060009 / 781250000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448964295109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_44 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (3302405557851 / 4000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561206381117 / 25000000000000 : ℝ))
      (E := (cell12756 ⟨44, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (3302405557851 / 4000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561206381117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_45 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82526245712307 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (35075460969 / 1562500000000 : ℝ))
      (E := (cell12756 ⟨45, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82526245712307 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (35075460969 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_46 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (16498475190009 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280604190543 / 12500000000000 : ℝ))
      (E := (cell12756 ⟨46, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (16498475190009 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280604190543 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_47 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (2576829050951 / 3125000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561209382707 / 25000000000000 : ℝ))
      (E := (cell12756 ⟨47, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (2576829050951 / 3125000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561209382707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_48 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41212353362279 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122420759737 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨48, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41212353362279 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122420759737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_49 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (10298863400457 / 12500000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122422773521 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨49, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (10298863400457 / 12500000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122422773521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_50 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (16471426207821 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448969910439 / 20000000000000 : ℝ))
      (E := (cell12756 ⟨50, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (16471426207821 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448969910439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_51 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82323378202427 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122426766151 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨51, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82323378202427 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122426766151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_52 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41144824332643 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448971508711 / 20000000000000 : ℝ))
      (E := (cell12756 ⟨52, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41144824332643 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (448971508711 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_53 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82255942399489 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280607690489 / 12500000000000 : ℝ))
      (E := (cell12756 ⟨53, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82255942399489 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280607690489 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_54 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41111129688491 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (89794623531 / 4000000000000 : ℝ))
      (E := (cell12756 ⟨54, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41111129688491 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (89794623531 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_55 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (20547149892463 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244869555997 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨55, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (20547149892463 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244869555997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_56 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82154962950327 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280609200089 / 12500000000000 : ℝ))
      (E := (cell12756 ⟨56, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82154962950327 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280609200089 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_57 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82121349490769 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244877600371 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨57, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82121349490769 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244877600371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_58 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (82087759163683 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244881610053 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨58, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (82087759163683 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244881610053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_59 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (20513547985427 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280610695791 / 12500000000000 : ℝ))
      (E := (cell12756 ⟨59, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (20513547985427 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280610695791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12757_40 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (16539188912801 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244688626041 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨40, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (16539188912801 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244688626041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_41 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41330978725157 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122346322087 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨41, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41330978725157 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122346322087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_42 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41313996962809 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122348326917 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨42, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41313996962809 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122348326917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_43 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82594053960267 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244700654109 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨43, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82594053960267 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244700654109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_44 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82560137524763 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244704643869 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨44, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82560137524763 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244704643869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_45 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (20631561147439 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244708621767 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨45, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (20631561147439 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244708621767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_46 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (20623093781511 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244712645131 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨46, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (20623093781511 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244712645131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_47 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82458529104569 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (112235832667 / 5000000000000 : ℝ))
      (E := (cell12757 ⟨47, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82458529104569 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (112235832667 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_48 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82424706496423 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244720644397 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨48, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82424706496423 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244720644397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_49 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (2059772681821 / 2500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244724675061 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨49, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (2059772681821 / 2500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244724675061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_50 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82357131405199 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561182170999 / 25000000000000 : ℝ))
      (E := (cell12757 ⟨50, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82357131405199 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561182170999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_51 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82323378865023 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244732668569 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨51, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82323378865023 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244732668569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_52 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41144824811989 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (224473668497 / 10000000000000 : ℝ))
      (E := (cell12757 ⟨52, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41144824811989 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (224473668497 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_53 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82255943653869 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244740671159 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨53, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82255943653869 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244740671159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_54 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (20555565231661 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448948936591 / 20000000000000 : ℝ))
      (E := (cell12757 ⟨54, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (20555565231661 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448948936591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_55 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (10273575176799 / 12500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448949743391 / 20000000000000 : ℝ))
      (E := (cell12757 ⟨55, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (10273575176799 / 12500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448949743391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_56 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82154965089339 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244752710419 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨56, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82154965089339 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244752710419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_57 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82121351923851 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (224475671861 / 10000000000000 : ℝ))
      (E := (cell12757 ⟨57, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82121351923851 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (224475671861 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_58 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82087761890431 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122380368753 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨58, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82087761890431 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122380368753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_59 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (82054194961719 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244764762873 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨59, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (82054194961719 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244764762873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12758_40 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (5168496371461 / 6250000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244567806567 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨40, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (5168496371461 / 6250000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244567806567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_41 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (10332744391283 / 12500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (140285738897 / 6250000000000 : ℝ))
      (E := (cell12758 ⟨41, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (10332744391283 / 12500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (140285738897 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_42 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82627991905731 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561143942889 / 25000000000000 : ℝ))
      (E := (cell12758 ⟨42, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82627991905731 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561143942889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_43 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82594052240131 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122289914831 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨43, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82594052240131 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122289914831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_44 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (16512027220793 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244583819143 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨44, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (16512027220793 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244583819143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_45 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82526243467883 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (44891755949 / 2000000000000 : ℝ))
      (E := (cell12758 ⟨45, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82526243467883 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (44891755949 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_46 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82492374302683 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122295910957 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨46, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82492374302683 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122295910957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_47 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82458528579311 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122297915953 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨47, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82458528579311 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122297915953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_48 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (41212353134429 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122299912717 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨48, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (41212353134429 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122299912717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_49 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (41195453671279 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448920771851 / 20000000000000 : ℝ))
      (E := (cell12758 ⟨49, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (41195453671279 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448920771851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_50 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82357131771791 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244607872031 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨50, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82357131771791 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244607872031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_51 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (41161689764041 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (280576482641 / 12500000000000 : ℝ))
      (E := (cell12758 ⟨51, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (41161689764041 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (280576482641 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_52 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (10286206322887 / 12500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244615882739 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨52, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (10286206322887 / 12500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244615882739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_53 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82255944908639 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244619874821 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨53, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82255944908639 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244619874821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_54 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (41111131238331 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244623893191 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨54, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (41111131238331 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244623893191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_55 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82188603259251 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122313937671 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨55, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82188603259251 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122313937671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_56 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (20538741807159 / 25000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122315938359 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨56, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (20538741807159 / 25000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122315938359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_57 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (82121354357181 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (8768108959 / 390625000000 : ℝ))
      (E := (cell12758 ⟨57, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (82121354357181 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (8768108959 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_58 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (5130485288587 / 6250000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (280579990209 / 12500000000000 : ℝ))
      (E := (cell12758 ⟨58, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (5130485288587 / 6250000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (280579990209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_59 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (20513549495477 / 25000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244643897793 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨59, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (20513549495477 / 25000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244643897793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12759_40 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (16539187864721 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244446983973 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨40, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (16539187864721 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244446983973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_41 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (16532390562207 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244450997447 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨41, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (16532390562207 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244450997447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_42 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (8262798988663 / 10000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (224445500383 / 10000000000000 : ℝ))
      (E := (cell12759 ⟨42, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (8262798988663 / 10000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (224445500383 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_43 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (10324256315093 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122229501103 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨43, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (10324256315093 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122229501103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_44 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (82560134683879 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (448892598289 / 20000000000000 : ℝ))
      (E := (cell12759 ⟨44, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (82560134683879 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (448892598289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_45 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41263121173343 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244467029069 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨45, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41263121173343 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244467029069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_46 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (20623093369991 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (224447105469 / 10000000000000 : ℝ))
      (E := (cell12759 ⟨46, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (20623093369991 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (224447105469 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_47 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (82458528054659 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (224447500761 / 10000000000000 : ℝ))
      (E := (cell12759 ⟨47, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (82458528054659 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (224447500761 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_48 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (82424706041861 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244479062587 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨48, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (82424706041861 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244479062587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_49 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (82390907412809 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244483040659 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨49, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (82390907412809 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244483040659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_50 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (82357132138881 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244487057313 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨50, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (82357132138881 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244487057313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_51 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41161690095801 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122245525487 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨51, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41161690095801 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122245525487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_52 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (1028620644283 / 1250000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (224449507783 / 10000000000000 : ℝ))
      (E := (cell12759 ⟨52, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (1028620644283 / 1250000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (224449507783 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_53 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (82255946163801 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1753514903 / 78125000000 : ℝ))
      (E := (cell12759 ⟨53, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (82255946163801 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1753514903 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_54 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41111132013517 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244503100821 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨54, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41111132013517 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244503100821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_55 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (8218860510443 / 10000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (280563386283 / 12500000000000 : ℝ))
      (E := (cell12759 ⟨55, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (8218860510443 / 10000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (280563386283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_56 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (10269371171027 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122255549807 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨56, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (10269371171027 / 12500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122255549807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_57 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (2053033919769 / 2500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244515125053 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨57, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (2053033919769 / 2500000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244515125053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_58 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (16417553468913 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (112225955169 / 5000000000000 : ℝ))
      (E := (cell12759 ⟨58, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (16417553468913 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (112225955169 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_59 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41027100501137 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (140282693093 / 6250000000000 : ℝ))
      (E := (cell12759 ⟨59, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41027100501137 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (140282693093 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12760_40 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82695936704691 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561081554253 / 25000000000000 : ℝ))
      (E := (cell12760 ⟨40, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82695936704691 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561081554253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_41 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82661950492627 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561082557059 / 25000000000000 : ℝ))
      (E := (cell12760 ⟨41, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82661950492627 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561082557059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_42 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41313993934157 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122167116529 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨42, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41313993934157 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122167116529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_43 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41297024401053 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561084557641 / 25000000000000 : ℝ))
      (E := (cell12760 ⟨43, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41297024401053 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561084557641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_44 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41280066632253 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244342278469 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨44, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41280066632253 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244342278469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_45 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (16505248245233 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122173128877 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨45, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (16505248245233 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122173128877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_46 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (16498474531577 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244350284569 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨46, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (16498474531577 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244350284569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_47 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (8245852753061 / 10000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (224435423937 / 10000000000000 : ℝ))
      (E := (cell12760 ⟨47, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (8245852753061 / 10000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (224435423937 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_48 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41212352907717 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122179148457 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨48, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41212352907717 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122179148457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_49 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82390907483593 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (14027264239 / 625000000000 : ℝ))
      (E := (cell12760 ⟨49, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82390907483593 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (14027264239 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_50 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (20589283126617 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140272893677 / 6250000000000 : ℝ))
      (E := (cell12760 ⟨50, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (20589283126617 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140272893677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_51 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (2572605651737 / 3125000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (448874059423 / 20000000000000 : ℝ))
      (E := (cell12760 ⟨51, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (2572605651737 / 3125000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (448874059423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_52 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82289652502609 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122187135121 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨52, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82289652502609 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122187135121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_53 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (10281993427419 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561094583319 / 25000000000000 : ℝ))
      (E := (cell12760 ⟨53, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (10281993427419 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561094583319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_54 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82222265577761 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122191152923 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨54, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82222265577761 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122191152923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_55 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (10273575868741 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (280548287827 / 12500000000000 : ℝ))
      (E := (cell12760 ⟨55, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (10273575868741 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (280548287827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_56 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82154971508081 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (280548789997 / 12500000000000 : ℝ))
      (E := (cell12760 ⟨56, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82154971508081 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (280548789997 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_57 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (82121359224587 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122197177053 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨57, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (82121359224587 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122197177053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_58 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (5130485629497 / 6250000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244398341801 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨58, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (5130485629497 / 6250000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244398341801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_59 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41027102011409 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244402337959 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨59, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41027102011409 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244402337959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12761_40 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41347967043317 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (448841101137 / 20000000000000 : ℝ))
      (E := (cell12761 ⟨40, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41347967043317 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (448841101137 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_41 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (258318588047 / 312500000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244209514719 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨41, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (258318588047 / 312500000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244209514719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_42 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82627985850783 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244213518041 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨42, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82627985850783 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244213518041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_43 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (10324255885527 / 12500000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122108757369 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨43, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (10324255885527 / 12500000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122108757369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_44 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (16512026369169 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (89768860147 / 4000000000000 : ℝ))
      (E := (cell12761 ⟨44, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (16512026369169 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (89768860147 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_45 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41263120053161 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122112771187 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨45, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41263120053161 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122112771187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_46 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82492371836447 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (44884590231 / 2000000000000 : ℝ))
      (E := (cell12761 ⟨46, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82492371836447 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (44884590231 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_47 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82458527007167 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244233527187 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨47, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82458527007167 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244233527187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_48 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (3296988223583 / 4000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244237528419 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨48, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (3296988223583 / 4000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244237528419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_49 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82390907554909 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561060393 / 25000000000 : ℝ))
      (E := (cell12761 ⟨49, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82390907554909 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561060393 / 25000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_50 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (10294641609319 / 12500000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244245537601 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨50, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (10294641609319 / 12500000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244245537601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_51 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (20580845380007 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122124770271 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨51, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (20580845380007 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122124770271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_52 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (16457930692601 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244253578047 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨52, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (16457930692601 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244253578047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_53 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82255948675293 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244257588071 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨53, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82255948675293 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244257588071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_54 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (82222267128843 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244261567347 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨54, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (82222267128843 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244261567347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_55 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (16437721759149 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244265571507 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨55, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (16437721759149 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244265571507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_56 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (20538743412057 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244269596937 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨56, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (20538743412057 / 25000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244269596937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_57 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41060680829331 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244273580663 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨57, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41060680829331 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244273580663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_58 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (1282621449993 / 1562500000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244277636939 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨58, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (1282621449993 / 1562500000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244277636939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_59 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (4102710352177 / 5000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (448856328641 / 20000000000000 : ℝ))
      (E := (cell12761 ⟨59, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (4102710352177 / 5000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (448856328641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12762_40 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (41347965734717 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244084791239 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨40, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (41347965734717 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244084791239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_41 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (41330972929137 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (56102219953 / 2500000000000 : ℝ))
      (E := (cell12762 ⟨41, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (41330972929137 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (56102219953 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_42 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (20656995958509 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (112204639999 / 5000000000000 : ℝ))
      (E := (cell12762 ⟨42, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (20656995958509 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (112204639999 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_43 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (3303761814683 / 4000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (8766003109 / 390625000000 : ℝ))
      (E := (cell12762 ⟨43, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (3303761814683 / 4000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (8766003109 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_44 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (10320016303487 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122050421803 / 50000000000000 : ℝ))
      (E := (cell12762 ⟨44, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (10320016303487 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122050421803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_45 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (41263119493577 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244104824061 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨45, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (41263119493577 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244104824061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_46 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (2577886594239 / 3125000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (140256803339 / 6250000000000 : ℝ))
      (E := (cell12762 ⟨46, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (2577886594239 / 3125000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (140256803339 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_47 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82458526484327 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448822562429 / 20000000000000 : ℝ))
      (E := (cell12762 ⟨47, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82458526484327 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448822562429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_48 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (16484941072857 / 20000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (56102920401 / 2500000000000 : ℝ))
      (E := (cell12762 ⟨48, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (16484941072857 / 20000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (56102920401 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_49 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82390907626759 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244120862971 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨49, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82390907626759 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244120862971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_50 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82357133243133 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244124832607 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨50, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82357133243133 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244124832607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_51 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (20580845546233 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (561032210067 / 25000000000000 : ℝ))
      (E := (cell12762 ⟨51, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (20580845546233 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (561032210067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_52 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (41144827211913 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (89765315327 / 4000000000000 : ℝ))
      (E := (cell12762 ⟨52, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (41144827211913 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (89765315327 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_53 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (658047599453 / 800000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244136899283 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨53, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (658047599453 / 800000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244136899283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_54 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82222268680279 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244140885327 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨54, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82222268680279 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244140885327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_55 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82188610641881 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448828979387 / 20000000000000 : ℝ))
      (E := (cell12762 ⟨55, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82188610641881 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448828979387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_56 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (4107748789433 / 5000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (561037217841 / 25000000000000 : ℝ))
      (E := (cell12762 ⟨56, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (4107748789433 / 5000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (561037217841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_57 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (16424272818597 / 20000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (224415292303 / 10000000000000 : ℝ))
      (E := (cell12762 ⟨57, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (16424272818597 / 20000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (224415292303 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_58 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (20521943881841 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244156929619 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨58, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (20521943881841 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2244156929619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_59 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (82054210064439 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (561040221707 / 25000000000000 : ℝ))
      (E := (cell12762 ⟨59, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (82054210064439 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (561040221707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12763_40 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (82695928853091 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243964132429 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨40, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (82695928853091 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243964132429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_41 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (10332742942791 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243968137219 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨41, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (10332742942791 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243968137219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_42 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (82627981818073 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243972137677 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨42, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (82627981818073 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243972137677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_43 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41297021825341 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280497016611 / 12500000000000 : ℝ))
      (E := (cell12763 ⟨43, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41297021825341 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280497016611 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_44 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (4128006450533 / 5000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243980121719 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨44, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (4128006450533 / 5000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243980121719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_45 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41263118934331 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243984161687 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨45, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41263118934331 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243984161687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_46 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (8249237019549 / 10000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121994066753 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨46, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (8249237019549 / 10000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121994066753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_47 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20614631490523 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243992153161 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨47, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20614631490523 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243992153161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_48 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (82424705139563 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243996159781 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨48, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (82424705139563 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243996159781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_49 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (82390907699141 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1122000075579 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨49, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (82390907699141 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1122000075579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_50 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (8235713361221 / 10000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1122002091927 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨50, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (8235713361221 / 10000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1122002091927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_51 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41161691425149 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (561002049073 / 25000000000000 : ℝ))
      (E := (cell12763 ⟨51, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41161691425149 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (561002049073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_52 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (5143103461567 / 6250000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2244012185627 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨52, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (5143103461567 / 6250000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2244012185627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_53 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41127975594173 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2244016207857 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨53, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41127975594173 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2244016207857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_54 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (82222270232069 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (8765703909 / 390625000000 : ℝ))
      (E := (cell12763 ⟨54, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (82222270232069 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (8765703909 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_55 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (16437722497667 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2244024219797 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨55, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (16437722497667 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2244024219797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_56 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41077488964687 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280503525299 / 12500000000000 : ℝ))
      (E := (cell12763 ⟨56, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41077488964687 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280503525299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_57 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20530341631889 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1795225763 / 80000000000 : ℝ))
      (E := (cell12763 ⟨57, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20530341631889 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1795225763 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_58 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (82087778255389 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (7012613187 / 312500000000 : ℝ))
      (E := (cell12763 ⟨58, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (82087778255389 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (7012613187 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_59 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20513553271379 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2244040246429 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨59, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20513553271379 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2244040246429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12764_40 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (20673981559401 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243843470503 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨40, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (20673981559401 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243843470503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_41 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41330970613601 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243847473237 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨41, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41330970613601 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243847473237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_42 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41313989901447 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243851472331 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨42, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41313989901447 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243851472331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_43 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (20648510483759 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243855525691 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨43, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (20648510483759 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243855525691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_44 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (10320015949267 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243859514557 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨44, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (10320015949267 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243859514557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_45 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (82526236750847 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243863496379 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨45, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (82526236750847 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243863496379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_46 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (20623092343993 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243867528483 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨46, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (20623092343993 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243867528483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_47 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (82458525440461 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560967887559 / 25000000000000 : ℝ))
      (E := (cell12764 ⟨47, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (82458525440461 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560967887559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_48 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (82424704915409 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121937779821 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨48, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (82424704915409 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121937779821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_49 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (16478181554411 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243879554489 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨49, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (16478181554411 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243879554489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_50 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (10294641747723 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (35060680193 / 1562500000000 : ℝ))
      (E := (cell12764 ⟨50, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (10294641747723 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (35060680193 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_51 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (20580845879031 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121943774803 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨51, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (20580845879031 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121943774803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_52 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (10286207043343 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243891544439 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨52, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (10286207043343 / 12500000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243891544439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_53 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (5140997027841 / 6250000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243895572851 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨53, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (5140997027841 / 6250000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243895572851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_54 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41111135892107 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (28048744657 / 1250000000000 : ℝ))
      (E := (cell12764 ⟨54, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41111135892107 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (28048744657 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_55 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (20547153583777 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121951799599 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨55, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (20547153583777 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121951799599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_56 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (20538745017593 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121953795009 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨56, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (20538745017593 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121953795009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_57 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (656970951699 / 800000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243911600281 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨57, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (656970951699 / 800000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243911600281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_58 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41043890491813 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560978906489 / 25000000000000 : ℝ))
      (E := (cell12764 ⟨58, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41043890491813 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560978906489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_59 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (82054216106769 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (224391960361 / 10000000000000 : ℝ))
      (E := (cell12764 ⟨59, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (82054216106769 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (224391960361 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12765_40 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82695923622973 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448744572843 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨40, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82695923622973 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448744572843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_41 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (645796397757 / 781250000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121863432477 / 50000000000000 : ℝ))
      (E := (cell12765 ⟨41, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (645796397757 / 781250000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121863432477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_42 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82627977788499 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243730862743 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨42, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82627977788499 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243730862743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_43 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82594040220139 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (70116716109 / 3125000000000 : ℝ))
      (E := (cell12765 ⟨43, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82594040220139 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (70116716109 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_44 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82560126178323 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243738904429 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨44, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82560126178323 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243738904429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_45 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82526235633707 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560935721753 / 25000000000000 : ℝ))
      (E := (cell12765 ⟨45, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82526235633707 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560935721753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_46 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41246184278547 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448749384113 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨46, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41246184278547 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448749384113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_47 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41229262459717 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448750188891 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨47, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41229262459717 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448750188891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_48 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82424704691823 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243754897741 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨48, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82424704691823 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243754897741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_49 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82390907845501 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243758955037 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨49, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82390907845501 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243758955037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_50 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (16471426870371 / 20000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (224376293709 / 10000000000000 : ℝ))
      (E := (cell12765 ⟨50, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (16471426870371 / 20000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (224376293709 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_51 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82323384182411 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (112188347961 / 5000000000000 : ℝ))
      (E := (cell12765 ⟨51, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82323384182411 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (112188347961 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_52 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82289657308841 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560942739903 / 25000000000000 : ℝ))
      (E := (cell12765 ⟨52, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82289657308841 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560942739903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_53 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82255953702957 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121887467603 / 50000000000000 : ℝ))
      (E := (cell12765 ⟨53, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82255953702957 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121887467603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_54 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (10277784167089 / 12500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (280472367727 / 12500000000000 : ℝ))
      (E := (cell12765 ⟨54, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (10277784167089 / 12500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (280472367727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_55 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (410943080911 / 500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121891488017 / 50000000000000 : ℝ))
      (E := (cell12765 ⟨55, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (410943080911 / 500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121891488017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_56 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (82154982211653 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560946743779 / 25000000000000 : ℝ))
      (E := (cell12765 ⟨56, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (82154982211653 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (560946743779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_57 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41060685698721 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (28047387429 / 1250000000000 : ℝ))
      (E := (cell12765 ⟨57, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41060685698721 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (28047387429 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_58 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (20521945928019 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (56094874261 / 2500000000000 : ℝ))
      (E := (cell12765 ⟨58, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (20521945928019 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (56094874261 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_59 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (410271095641 / 500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243799017569 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨59, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (410271095641 / 500000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243799017569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12766_40 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41347960504599 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560900578391 / 25000000000000 : ℝ))
      (E := (cell12766 ⟨40, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41347960504599 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560900578391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_41 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (8266193659941 / 10000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243606312369 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨41, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (8266193659941 / 10000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243606312369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_42 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (82627975774887 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448722061783 / 20000000000000 : ℝ))
      (E := (cell12766 ⟨42, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (82627975774887 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448722061783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_43 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (20648509626497 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121807151141 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨43, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (20648509626497 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121807151141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_44 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (82560124763221 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (112180917509 / 5000000000000 : ℝ))
      (E := (cell12766 ⟨44, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (82560124763221 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (112180917509 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_45 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41263117258621 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121811166793 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨45, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41263117258621 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121811166793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_46 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41246183869427 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121813154877 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨46, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41246183869427 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121813154877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_47 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (8245852439901 / 10000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448726067163 / 20000000000000 : ℝ))
      (E := (cell12766 ⟨47, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (8245852439901 / 10000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448726067163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_48 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (20606176117201 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121817175451 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨48, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (20606176117201 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121817175451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_49 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (2059772697987 / 2500000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243638352799 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨49, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (2059772697987 / 2500000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243638352799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_50 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (82357134722421 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121821169541 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨50, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (82357134722421 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121821169541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_51 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41161692424579 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560911591531 / 25000000000000 : ℝ))
      (E := (cell12766 ⟨51, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41161692424579 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560911591531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_52 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41144829135681 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243650372111 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨52, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41144829135681 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243650372111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_53 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41127977480423 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121827176991 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨53, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41127977480423 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121827176991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_54 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (20555568722391 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (35057161993 / 1562500000000 : ℝ))
      (E := (cell12766 ⟨54, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (20555568722391 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (35057161993 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_55 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (82188618029609 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243662409411 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨55, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (82188618029609 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243662409411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_56 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (1283671630519 / 1562500000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121833208407 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨56, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (1283671630519 / 1562500000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121833208407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_57 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (20530343458189 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121835192933 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨57, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (20530343458189 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121835192933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_58 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (82087786440737 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (112183721541 / 5000000000000 : ℝ))
      (E := (cell12766 ⟨58, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (82087786440737 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (112183721541 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_59 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (82054222149807 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243678429107 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨59, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (82054222149807 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243678429107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12767_40 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82695918396279 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (11217408799 / 500000000000 : ℝ))
      (E := (cell12767 ⟨40, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82695918396279 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (11217408799 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_41 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82661934286743 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243485756709 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨41, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82661934286743 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243485756709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_42 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82627973762059 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243489752047 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨42, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82627973762059 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243489752047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_43 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (16518807358517 / 20000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243493803721 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨43, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (16518807358517 / 20000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243493803721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_44 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82560123348831 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121748896483 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨44, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82560123348831 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121748896483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_45 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (20631558350363 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243501777231 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨45, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (20631558350363 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243501777231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_46 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (41246183460627 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (28043822673 / 1250000000000 : ℝ))
      (E := (cell12767 ⟨46, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (41246183460627 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (28043822673 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_47 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82458523879189 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (56087744581 / 2500000000000 : ℝ))
      (E := (cell12767 ⟨47, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82458523879189 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (56087744581 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_48 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (41212352123177 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560878450311 / 25000000000000 : ℝ))
      (E := (cell12767 ⟨48, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (41212352123177 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560878450311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_49 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (8239090799399 / 10000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121758903373 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨49, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (8239090799399 / 10000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121758903373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_50 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (20589283773371 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243521797317 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨50, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (20589283773371 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243521797317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_51 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (41161692758183 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243525829331 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨51, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (41161692758183 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243525829331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_52 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82289659234309 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560882460243 / 25000000000000 : ℝ))
      (E := (cell12767 ⟨52, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82289659234309 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560882460243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_53 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (658047649753 / 800000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121766914591 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨53, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (658047649753 / 800000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121766914591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_54 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82222276442769 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560884462443 / 25000000000000 : ℝ))
      (E := (cell12767 ⟨54, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82222276442769 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560884462443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_55 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82188619877337 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (89741673609 / 4000000000000 : ℝ))
      (E := (cell12767 ⟨55, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82188619877337 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (89741673609 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_56 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (41077493247531 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121772927993 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨56, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (41077493247531 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121772927993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_57 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82121376268317 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560887473307 / 25000000000000 : ℝ))
      (E := (cell12767 ⟨57, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82121376268317 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560887473307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_58 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (82087789169611 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (448710777749 / 20000000000000 : ℝ))
      (E := (cell12767 ⟨58, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (82087789169611 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (448710777749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_59 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (10256778146449 / 12500000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243557897427 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨59, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (10256778146449 / 12500000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243557897427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12768_40 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (16539183156843 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560840315419 / 25000000000000 : ℝ))
      (E := (cell12768 ⟨40, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (16539183156843 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560840315419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_41 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (5166370748431 / 6250000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243365256749 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨41, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (5166370748431 / 6250000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243365256749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_42 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41313985875007 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243369250941 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨42, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41313985875007 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243369250941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_43 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82594035079929 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243373243333 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨43, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82594035079929 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243373243333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_44 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82560121935151 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (448675458327 / 20000000000000 : ℝ))
      (E := (cell12768 ⟨44, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82560121935151 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (448675458327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_45 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82526232286337 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243381276819 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨45, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82526232286337 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243381276819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_46 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41246183052147 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243385256139 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨46, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41246183052147 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243385256139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_47 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (20614630839993 / 25000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243389286727 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨47, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (20614630839993 / 25000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243389286727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_48 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (8242470402447 / 10000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243393307711 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨48, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (8242470402447 / 10000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243393307711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_49 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82390908069031 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560849329219 / 25000000000000 : ℝ))
      (E := (cell12768 ⟨49, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82390908069031 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560849329219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_50 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41178567732521 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560850327949 / 25000000000000 : ℝ))
      (E := (cell12768 ⟨50, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41178567732521 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560850327949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_51 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41161693092017 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243405289829 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨51, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41161693092017 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243405289829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_52 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82289660197679 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243409307163 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨52, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82289660197679 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243409307163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_53 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (2570498671181 / 3125000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121706650873 / 50000000000000 : ℝ))
      (E := (cell12768 ⟨53, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (2570498671181 / 3125000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121706650873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_54 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (10277784749541 / 12500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243417329391 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨54, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (10277784749541 / 12500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243417329391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_55 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82188621725383 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121710663791 / 50000000000000 : ℝ))
      (E := (cell12768 ⟨55, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82188621725383 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121710663791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_56 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82154988637191 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (28042816897 / 1250000000000 : ℝ))
      (E := (cell12768 ⟨56, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82154988637191 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (28042816897 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_57 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41060689352063 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (448685867789 / 20000000000000 : ℝ))
      (E := (cell12768 ⟨57, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41060689352063 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (448685867789 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_58 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82087791898697 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (448686668843 / 20000000000000 : ℝ))
      (E := (cell12768 ⟨58, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82087791898697 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (448686668843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_59 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (82054228193553 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243437363329 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨59, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (82054228193553 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243437363329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12769_40 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41347956586503 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243240760441 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨40, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41347956586503 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243240760441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_41 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82661929663867 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121622376857 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨41, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82661929663867 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121622376857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_42 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (40345688349 / 48828125000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560812186699 / 25000000000000 : ℝ))
      (E := (cell12769 ⟨42, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (40345688349 / 48828125000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560812186699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_43 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (4129701668401 / 5000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243252797593 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨43, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (4129701668401 / 5000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243252797593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_44 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41280060261091 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243256787339 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨44, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41280060261091 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243256787339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_45 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82526231171897 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (56081519337 / 2500000000000 : ℝ))
      (E := (cell12769 ⟨45, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82526231171897 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (56081519337 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_46 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82492365287971 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121632406669 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨46, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82492365287971 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121632406669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_47 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82458522841357 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243268787361 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨47, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82458522841357 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243268787361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_48 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41212351901577 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (14020455071 / 625000000000 : ℝ))
      (E := (cell12769 ⟨48, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41212351901577 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (14020455071 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_49 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (20597727036151 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121638412113 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨49, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (20597727036151 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121638412113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_50 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82357135837097 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243280823529 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨50, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82357135837097 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243280823529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_51 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41161693426081 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (280410600829 / 12500000000000 : ℝ))
      (E := (cell12769 ⟨51, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41161693426081 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (280410600829 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_52 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41144830580737 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121644414859 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨52, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41144830580737 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121644414859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_53 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82255958736849 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121646415367 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨53, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82255958736849 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121646415367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_54 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82222279550241 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (448659373099 / 20000000000000 : ℝ))
      (E := (cell12769 ⟨54, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82222279550241 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (448659373099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_55 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82188623573747 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121650435741 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨55, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82188623573747 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121650435741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_56 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82154990779603 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243304845007 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨56, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82154990779603 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243304845007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_57 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (82121381140181 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (140206802583 / 6250000000000 : ℝ))
      (E := (cell12769 ⟨57, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (82121381140181 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (140206802583 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_58 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (16417558925599 / 20000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243312856409 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨58, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (16417558925599 / 20000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243312856409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_59 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (8205423121569 / 10000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121658443007 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨59, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (8205423121569 / 10000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121658443007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12770_40 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (20673977640663 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (70097509839 / 3125000000000 : ℝ))
      (E := (cell12770 ⟨40, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (20673977640663 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (70097509839 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_41 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (82661927353657 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121562153191 / 50000000000000 : ℝ))
      (E := (cell12770 ⟨41, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (82661927353657 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121562153191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_42 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (5164247983017 / 6250000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (140195518651 / 6250000000000 : ℝ))
      (E := (cell12770 ⟨42, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (5164247983017 / 6250000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (140195518651 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_43 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (82594031656857 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243132348853 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨43, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (82594031656857 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243132348853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_44 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (20640029777481 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243136338927 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨44, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (20640029777481 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243136338927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_45 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (20631557514533 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560785081521 / 25000000000000 : ℝ))
      (E := (cell12770 ⟨45, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (20631557514533 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560785081521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_46 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (2577886389759 / 3125000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121572183823 / 50000000000000 : ℝ))
      (E := (cell12770 ⟨46, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (2577886389759 / 3125000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121572183823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_47 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (16491704464669 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243148344059 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨47, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (16491704464669 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243148344059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_48 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (20606175895601 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121576185567 / 50000000000000 : ℝ))
      (E := (cell12770 ⟨48, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (20606175895601 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121576185567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_49 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (20597727055177 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (28039454847 / 1250000000000 : ℝ))
      (E := (cell12770 ⟨49, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (20597727055177 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (28039454847 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_50 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41178568104823 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243160391509 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨50, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41178568104823 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243160391509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_51 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (329293550083 / 400000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (112158218987 / 5000000000000 : ℝ))
      (E := (cell12770 ⟨51, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (329293550083 / 400000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (112158218987 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_52 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41144831062847 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243168408637 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨52, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41144831062847 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243168408637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_53 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41127979998147 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560793104037 / 25000000000000 : ℝ))
      (E := (cell12770 ⟨53, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41127979998147 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560793104037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_54 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41111140552253 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121588199501 / 50000000000000 : ℝ))
      (E := (cell12770 ⟨54, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41111140552253 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121588199501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_55 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (82188625422429 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243180412821 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨55, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (82188625422429 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243180412821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_56 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (10269374115287 / 12500000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (112159219743 / 5000000000000 : ℝ))
      (E := (cell12770 ⟨56, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (10269374115287 / 12500000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (112159219743 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_57 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (20530345894121 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243188400373 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨57, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (20530345894121 / 25000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243188400373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_58 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (1282621833711 / 1562500000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121596212663 / 50000000000000 : ℝ))
      (E := (cell12770 ⟨58, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (1282621833711 / 1562500000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121596212663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_59 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (16410846847601 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243196406281 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨59, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (16410846847601 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243196406281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12771_40 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82695907953153 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (70093745817 / 3125000000000 : ℝ))
      (E := (cell12771 ⟨40, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82695907953153 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (70093745817 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_41 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (41330962522133 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121501957377 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨41, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (41330962522133 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121501957377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_42 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (41313982859287 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (11215039529 / 500000000000 : ℝ))
      (E := (cell12771 ⟨42, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (41313982859287 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (11215039529 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_43 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (2064850748661 / 2500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243011897113 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨43, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (2064850748661 / 2500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243011897113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_44 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (10320014712297 / 12500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243015887553 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨44, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (10320014712297 / 12500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243015887553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_45 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82526228945041 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121509967317 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨45, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82526228945041 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121509967317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_46 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82492363657243 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448604783813 / 20000000000000 : ℝ))
      (E := (cell12771 ⟨46, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82492363657243 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448604783813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_47 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (5153657612871 / 6250000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (280378494603 / 12500000000000 : ℝ))
      (E := (cell12771 ⟨47, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (5153657612871 / 6250000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (280378494603 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_48 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82424703362221 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243031928093 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨48, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82424703362221 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243031928093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_49 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82390908297343 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (560758987129 / 25000000000000 : ℝ))
      (E := (cell12771 ⟨49, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82390908297343 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (560758987129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_50 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82357136582691 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121519978373 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨50, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82357136582691 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121519978373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_51 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82323388189797 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243043950143 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨51, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82323388189797 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243043950143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_52 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82289663090337 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243047984887 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨52, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82289663090337 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243047984887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_53 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (82255961256127 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243051998929 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨53, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (82255961256127 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243051998929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_54 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (657778261273 / 800000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243055988993 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨54, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (657778261273 / 800000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243055988993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_55 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (20547156817857 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121530005353 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨55, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (20547156817857 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121530005353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_56 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (10269374383159 / 12500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121532000659 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨56, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (10269374383159 / 12500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121532000659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_57 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (41060693006517 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243068016083 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨57, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (41060693006517 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243068016083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_58 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (3283512003489 / 4000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243071991791 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨58, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (3283512003489 / 4000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2243071991791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_59 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (16410847452099 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121538021267 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨59, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (16410847452099 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121538021267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12772_40 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (20673976336127 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (448575894617 / 20000000000000 : ℝ))
      (E := (cell12772 ⟨40, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (20673976336127 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (448575894617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_41 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82661922735693 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242883520053 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨41, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82661922735693 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242883520053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_42 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82627963709659 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242887510147 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨42, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82627963709659 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242887510147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_43 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (8259402823677 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121445750599 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨43, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (8259402823677 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121445750599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_44 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (41280058143769 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (35045242983 / 1562500000000 : ℝ))
      (E := (cell12772 ⟨44, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (41280058143769 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (35045242983 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_45 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82526227832623 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (112144977013 / 5000000000000 : ℝ))
      (E := (cell12772 ⟨45, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82526227832623 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (112144977013 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_46 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (20623090710709 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242903526491 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨46, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (20623090710709 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242903526491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_47 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82458521289129 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140181722921 / 6250000000000 : ℝ))
      (E := (cell12772 ⟨47, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82458521289129 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140181722921 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_48 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (16484940628521 / 20000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242911541177 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨48, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (16484940628521 / 20000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242911541177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_49 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82390908374509 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121457782729 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨49, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82390908374509 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121457782729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_50 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82357136956231 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (224291957823 / 10000000000000 : ℝ))
      (E := (cell12772 ⟨50, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82357136956231 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (224291957823 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_51 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (10290423607413 / 12500000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560730894213 / 25000000000000 : ℝ))
      (E := (cell12772 ⟨51, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (10290423607413 / 12500000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560730894213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_52 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (20572416013851 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242927558469 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨52, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (20572416013851 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242927558469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_53 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82255962516349 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560732894769 / 25000000000000 : ℝ))
      (E := (cell12772 ⟨53, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82255962516349 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560732894769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_54 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (5138892763381 / 6250000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (224293557639 / 10000000000000 : ℝ))
      (E := (cell12772 ⟨54, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (5138892763381 / 6250000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (224293557639 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_55 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (10273578640093 / 12500000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242939606031 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨55, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (10273578640093 / 12500000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242939606031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_56 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (8215499720853 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560735901313 / 25000000000000 : ℝ))
      (E := (cell12772 ⟨56, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (8215499720853 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (560735901313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_57 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (8212138844983 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121473814653 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨57, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (8212138844983 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121473814653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_58 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (82087802817157 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121475807491 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨58, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (82087802817157 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121475807491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_59 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (41027120141581 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242955617169 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨59, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (41027120141581 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242955617169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12773_40 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (82695902736717 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242759135671 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨40, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (82695902736717 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242759135671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_41 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (82661920427937 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242763122281 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨41, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (82661920427937 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242763122281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_42 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (3305118468061 / 4000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121383585131 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨42, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (3305118468061 / 4000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121383585131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_43 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16518805305569 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242771161111 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨43, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16518805305569 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242771161111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_44 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (82560114877409 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242775152463 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨44, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (82560114877409 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242775152463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_45 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (1031577834011 / 1250000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242779142961 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨45, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (1031577834011 / 1250000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242779142961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_46 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (82492362029067 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (89711327597 / 4000000000000 : ℝ))
      (E := (cell12773 ⟨46, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (82492362029067 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (89711327597 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_47 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (20614630193231 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242787173799 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨47, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (20614630193231 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242787173799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_48 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16484940584711 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242791210391 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨48, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16484940584711 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242791210391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_49 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16478181690441 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280349397453 / 12500000000000 : ℝ))
      (E := (cell12773 ⟨49, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16478181690441 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280349397453 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_50 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (41178568665133 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242799196973 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨50, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (41178568665133 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242799196973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_51 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (8232338952927 / 10000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280350400107 / 12500000000000 : ℝ))
      (E := (cell12773 ⟨51, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (8232338952927 / 10000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280350400107 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_52 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16457933004179 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242807188417 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨52, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16457933004179 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242807188417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_53 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (82255963776959 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (560702803913 / 25000000000000 : ℝ))
      (E := (cell12773 ⟨53, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (82255963776959 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (560702803913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_54 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (4111114288471 / 5000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242815220273 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨54, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (4111114288471 / 5000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242815220273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_55 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (41094315485189 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (140176203619 / 6250000000000 : ℝ))
      (E := (cell12773 ⟨55, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (41094315485189 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (140176203619 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_56 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (8215499935207 / 10000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242823265793 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨56, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (8215499935207 / 10000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242823265793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_57 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (82121390886873 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121413620021 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨57, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (82121390886873 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121413620021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_58 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (82087805547301 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121415617861 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨58, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (82087805547301 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121415617861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_59 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (20513560826501 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (140177203037 / 6250000000000 : ℝ))
      (E := (cell12773 ⟨59, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (20513560826501 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (140177203037 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12774_40 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (4134795006489 / 5000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (44852775903 / 2000000000000 : ℝ))
      (E := (cell12774 ⟨40, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (4134795006489 / 5000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (44852775903 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_41 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82661918121 / 100000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121321419497 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨41, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82661918121 / 100000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121321419497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_42 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82627959694173 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (140165426709 / 6250000000000 : ℝ))
      (E := (cell12774 ⟨42, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82627959694173 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (140165426709 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_43 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41297012409833 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121325409013 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨43, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41297012409833 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121325409013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_44 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82560113467991 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121327404951 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨44, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82560113467991 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121327404951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_45 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (8252622560981 / 10000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242658860483 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨45, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (8252622560981 / 10000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242658860483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_46 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (16498472243187 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242662850473 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨46, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (16498472243187 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242662850473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_47 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82458520257321 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (224266683693 / 10000000000000 : ℝ))
      (E := (cell12774 ⟨47, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82458520257321 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (224266683693 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_48 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82424702705071 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242670876791 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨48, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82424702705071 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242670876791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_49 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (321839486447 / 390625000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121337424989 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨49, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (321839486447 / 390625000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121337424989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_50 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (16471427540959 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121339435983 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨50, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (16471427540959 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121339435983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_51 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (16464678039939 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242682881171 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨51, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (16464678039939 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242682881171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_52 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (8228966598681 / 10000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448537374947 / 20000000000000 : ℝ))
      (E := (cell12774 ⟨52, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (8228966598681 / 10000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448537374947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_53 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82255965037957 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242690908657 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨53, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82255965037957 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242690908657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_54 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82222287325097 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448538984129 / 20000000000000 : ℝ))
      (E := (cell12774 ⟨54, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82222287325097 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448538984129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_55 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82188632820329 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121349453609 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨55, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82188632820329 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121349453609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_56 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (20538750373973 / 25000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560675730953 / 25000000000000 : ℝ))
      (E := (cell12774 ⟨56, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (20538750373973 / 25000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560675730953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_57 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41060696662081 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121353453723 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨57, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41060696662081 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121353453723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_58 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (10260976034707 / 12500000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242710913189 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨58, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (10260976034707 / 12500000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242710913189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_59 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (82054246329023 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242714936801 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨59, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (82054246329023 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242714936801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

end BstLean.Part268
