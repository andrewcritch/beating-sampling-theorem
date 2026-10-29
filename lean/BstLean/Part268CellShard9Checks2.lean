import BstLean.Part268CellShard9Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12575_40 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82696436064999 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267258757689 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨40, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82696436064999 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267258757689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_41 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82662393634639 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133631394891 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨41, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82662393634639 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133631394891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_42 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (41314187434811 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267266803373 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨42, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (41314187434811 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267266803373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_43 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (41297189870081 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (90690831913 / 4000000000000 : ℝ))
      (E := (cell12575 ⟨43, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (41297189870081 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (90690831913 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_44 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82560408216621 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267274772279 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨44, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82560408216621 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267274772279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_45 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (10315807533689 / 12500000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133639392257 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨45, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (10315807533689 / 12500000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133639392257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_46 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (10311566983687 / 12500000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267282774431 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨46, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (10311566983687 / 12500000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267282774431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_47 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82458634987383 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267286799421 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨47, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82458634987383 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267286799421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_48 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (5151547349633 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566822699727 / 25000000000000 : ℝ))
      (E := (cell12575 ⟨48, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (5151547349633 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566822699727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_49 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82390903660833 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267294829899 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨49, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82390903660833 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267294829899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_50 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (10294634144843 / 12500000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267298831343 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨50, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (10294634144843 / 12500000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267298831343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_51 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82323266059253 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267302800873 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨51, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82323266059253 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267302800873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_52 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82289482333893 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267306794931 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨52, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82289482333893 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267306794931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_53 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82255721954343 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267310810797 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨53, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82255721954343 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267310810797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_54 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (4111099244621 / 5000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (283414355693 / 12500000000000 : ℝ))
      (E := (cell12575 ⟨54, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (4111099244621 / 5000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (283414355693 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_55 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (20547067780021 / 25000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267318836943 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨55, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (20547067780021 / 25000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267318836943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_56 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (20538645152359 / 25000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267322840687 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨56, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (20538645152359 / 25000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267322840687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_57 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82120913332713 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133663426611 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨57, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82120913332713 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133663426611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_58 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (16417453852459 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133665405811 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨58, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (16417453852459 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133665405811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_59 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (10256706046337 / 12500000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566833707553 / 25000000000000 : ℝ))
      (E := (cell12575 ⟨59, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (10256706046337 / 12500000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566833707553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12576_40 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (1653928665679 / 2000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267131295827 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨40, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (1653928665679 / 2000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267131295827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_41 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (82662391160891 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133567657899 / 50000000000000 : ℝ))
      (E := (cell12576 ⟨41, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (82662391160891 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133567657899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_42 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (82628372702751 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (141696207373 / 6250000000000 : ℝ))
      (E := (cell12576 ⟨42, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (82628372702751 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (141696207373 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_43 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (82594377879743 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267143301699 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨43, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (82594377879743 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267143301699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_44 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (10320050832779 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (14169670781 / 625000000000 : ℝ))
      (E := (cell12576 ⟨44, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (10320050832779 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (14169670781 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_45 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (82526459020731 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133575663947 / 50000000000000 : ℝ))
      (E := (cell12576 ⟨45, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (82526459020731 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133575663947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_46 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41246267462951 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283394413651 / 12500000000000 : ℝ))
      (E := (cell12576 ⟨46, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41246267462951 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283394413651 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_47 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (16491726869711 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267159326291 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨47, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (16491726869711 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267159326291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_48 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (16484951451929 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283395414821 / 12500000000000 : ℝ))
      (E := (cell12576 ⟨48, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (16484951451929 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283395414821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_49 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (82390903630277 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267167284097 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨49, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (82390903630277 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267167284097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_50 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (5147317089481 / 6250000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566792834667 / 25000000000000 : ℝ))
      (E := (cell12576 ⟨50, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (5147317089481 / 6250000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566792834667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_51 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (16464653327059 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (70849228221 / 3125000000000 : ℝ))
      (E := (cell12576 ⟨51, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (16464653327059 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (70849228221 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_52 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (82289483212609 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133589646349 / 50000000000000 : ℝ))
      (E := (cell12576 ⟨52, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (82289483212609 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133589646349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_53 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (20563930783829 / 25000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283397913103 / 12500000000000 : ℝ))
      (E := (cell12576 ⟨53, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (20563930783829 / 25000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283397913103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_54 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (16444397275047 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133593668261 / 50000000000000 : ℝ))
      (E := (cell12576 ⟨54, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (16444397275047 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133593668261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_55 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41094136452163 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566797831391 / 25000000000000 : ℝ))
      (E := (cell12576 ⟨55, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41094136452163 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566797831391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_56 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (8215458269469 / 10000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133597663821 / 50000000000000 : ℝ))
      (E := (cell12576 ⟨56, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (8215458269469 / 10000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133597663821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_57 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (82120915718567 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1416999587 / 62500000000 : ℝ))
      (E := (cell12576 ⟨57, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (82120915718567 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1416999587 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_58 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (5130454496771 / 6250000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283400419559 / 12500000000000 : ℝ))
      (E := (cell12576 ⟨58, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (5130454496771 / 6250000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283400419559 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_59 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (2564176604891 / 3125000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267207375487 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨59, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (2564176604891 / 3125000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267207375487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12577_40 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41348215251903 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566750957669 / 25000000000000 : ℝ))
      (E := (cell12577 ⟨40, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41348215251903 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566750957669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_41 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82662388688011 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566751959641 / 25000000000000 : ℝ))
      (E := (cell12577 ⟨41, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82662388688011 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566751959641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_42 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (8262837053671 / 10000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267011829351 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨42, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (8262837053671 / 10000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267011829351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_43 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82594376020117 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453403172241 / 20000000000000 : ℝ))
      (E := (cell12577 ⟨43, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82594376020117 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453403172241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_44 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82560405108599 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453403974901 / 20000000000000 : ℝ))
      (E := (cell12577 ⟨44, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82560405108599 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453403974901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_45 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (20631614443167 / 25000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267023868177 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨45, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (20631614443167 / 25000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267023868177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_46 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (20623133495747 / 25000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133513920463 / 50000000000000 : ℝ))
      (E := (cell12577 ⟨46, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (20623133495747 / 25000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133513920463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_47 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82458633710369 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133515925071 / 50000000000000 : ℝ))
      (E := (cell12577 ⟨47, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82458633710369 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133515925071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_48 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82424756925769 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453407167049 / 20000000000000 : ℝ))
      (E := (cell12577 ⟨48, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82424756925769 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453407167049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_49 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82390903600289 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453407970649 / 20000000000000 : ℝ))
      (E := (cell12577 ⟨49, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82390903600289 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453407970649 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_50 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (4117853685259 / 5000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133521921543 / 50000000000000 : ℝ))
      (E := (cell12577 ⟨50, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (4117853685259 / 5000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133521921543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_51 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (10290408401479 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267047861397 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨51, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (10290408401479 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267047861397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_52 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82289484091783 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267051846651 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨52, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82289484091783 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267051846651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_53 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (8225572431671 / 10000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133527927549 / 50000000000000 : ℝ))
      (E := (cell12577 ⟨53, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (8225572431671 / 10000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133527927549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_54 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41110993929217 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267059883809 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨54, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41110993929217 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267059883809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_55 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (16437654937783 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566765967639 / 25000000000000 : ℝ))
      (E := (cell12577 ⟨55, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (16437654937783 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566765967639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_56 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (16430916956051 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267067871029 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨56, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (16430916956051 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267067871029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_57 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (16424183620939 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283383985209 / 12500000000000 : ℝ))
      (E := (cell12577 ⟨57, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (16424183620939 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283383985209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_58 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41043637317307 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267075898717 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨58, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41043637317307 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2267075898717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_59 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (641044174551 / 781250000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453415983639 / 20000000000000 : ℝ))
      (E := (cell12577 ⟨59, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (641044174551 / 781250000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453415983639 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12578_40 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (10337053465571 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566719105243 / 25000000000000 : ℝ))
      (E := (cell12578 ⟨40, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (10337053465571 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566719105243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_41 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41331193107999 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133440208419 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨41, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41331193107999 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133440208419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_42 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41314184185749 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (141680278443 / 6250000000000 : ℝ))
      (E := (cell12578 ⟨42, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41314184185749 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (141680278443 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_43 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (20648593540321 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283361059543 / 12500000000000 : ℝ))
      (E := (cell12578 ⟨43, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (20648593540321 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283361059543 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_44 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (2064010088893 / 2500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266892420917 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨44, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (2064010088893 / 2500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266892420917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_45 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (82526456525323 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266896464217 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨45, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (82526456525323 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266896464217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_46 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41246266520377 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266900428463 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨46, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41246266520377 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266900428463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_47 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (82458633072827 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266904429871 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨47, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (82458633072827 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266904429871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_48 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41212378296249 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566727116697 / 25000000000000 : ℝ))
      (E := (cell12578 ⟨48, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41212378296249 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566727116697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_49 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (82390903570871 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566728119599 / 25000000000000 : ℝ))
      (E := (cell12578 ⟨49, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (82390903570871 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566728119599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_50 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (16471414795839 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266916462541 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨50, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (16471414795839 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266916462541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_51 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (1286301059201 / 1562500000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283365059481 / 12500000000000 : ℝ))
      (E := (cell12578 ⟨51, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (1286301059201 / 1562500000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283365059481 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_52 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41144742485707 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283365557099 / 12500000000000 : ℝ))
      (E := (cell12578 ⟨52, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41144742485707 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283365557099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_53 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (3290229019941 / 4000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133464230811 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨53, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (3290229019941 / 4000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133464230811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_54 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (1284718583469 / 1562500000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (141683280463 / 6250000000000 : ℝ))
      (E := (cell12578 ⟨54, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (1284718583469 / 1562500000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (141683280463 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_55 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (82188276473851 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266936471919 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨55, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (82188276473851 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266936471919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_56 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (8215458686613 / 10000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266940470849 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨56, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (8215458686613 / 10000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266940470849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_57 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (10265115061387 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266944480637 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨57, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (10265115061387 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266944480637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_58 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (10260909665141 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133474248759 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨58, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (10260909665141 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133474248759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_59 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (82053657328743 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (28336906469 / 1250000000000 : ℝ))
      (E := (cell12578 ⟨59, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (82053657328743 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (28336906469 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12579_40 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41348212473117 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133374533359 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨40, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41348212473117 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133374533359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_41 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82662383744853 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (283344138673 / 12500000000000 : ℝ))
      (E := (cell12579 ⟨41, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82662383744853 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (283344138673 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_42 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82628366207117 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141672317351 / 6250000000000 : ℝ))
      (E := (cell12579 ⟨42, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82628366207117 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141672317351 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_43 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82594372303243 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266761088313 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨43, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82594372303243 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266761088313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_44 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82560402003597 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453353016371 / 20000000000000 : ℝ))
      (E := (cell12579 ⟨44, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82560402003597 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453353016371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_45 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (16505291055739 / 20000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141673069751 / 6250000000000 : ℝ))
      (E := (cell12579 ⟨45, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (16505291055739 / 20000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141673069751 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_46 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82492532099201 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (113338653591 / 5000000000000 : ℝ))
      (E := (cell12579 ⟨46, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82492532099201 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (113338653591 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_47 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82458632435927 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453355424877 / 20000000000000 : ℝ))
      (E := (cell12579 ⟨47, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82458632435927 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453355424877 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_48 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (10303094532479 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266781095353 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨48, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (10303094532479 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266781095353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_49 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (4119545177101 / 5000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (35418517197 / 1562500000000 : ℝ))
      (E := (cell12579 ⟨49, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (4119545177101 / 5000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (35418517197 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_50 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41178537126871 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566697269773 / 25000000000000 : ℝ))
      (E := (cell12579 ⟨50, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41178537126871 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566697269773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_51 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (8232326836639 / 10000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453358617487 / 20000000000000 : ℝ))
      (E := (cell12579 ⟨51, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (8232326836639 / 10000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453358617487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_52 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82289485851503 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566699280781 / 25000000000000 : ℝ))
      (E := (cell12579 ⟨52, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82289485851503 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566699280781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_53 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (2056393167019 / 2500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133400562199 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨53, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (2056393167019 / 2500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133400562199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_54 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41110995412991 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (56670128683 / 2500000000000 : ℝ))
      (E := (cell12579 ⟨54, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41110995412991 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (56670128683 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_55 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82188278259133 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266809129659 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨55, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82188278259133 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266809129659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_56 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (16430917790463 / 20000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453362625421 / 20000000000000 : ℝ))
      (E := (cell12579 ⟨56, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (16430917790463 / 20000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453362625421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_57 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (8212092287777 / 10000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266817136101 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨57, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (8212092287777 / 10000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266817136101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_58 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82087280007879 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133410576439 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨58, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82087280007879 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133410576439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_59 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82053660315159 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266825114281 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨59, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82053660315159 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266825114281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12580_40 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41348211084403 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (283327720989 / 12500000000000 : ℝ))
      (E := (cell12580 ⟨40, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41348211084403 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (283327720989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_41 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (3306495250983 / 4000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266625739923 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨41, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (3306495250983 / 4000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266625739923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_42 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (16525672808713 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266629755717 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨42, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (16525672808713 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266629755717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_43 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41297185222997 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566658438979 / 25000000000000 : ℝ))
      (E := (cell12580 ⟨43, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41297185222997 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566658438979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_44 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (20640100113057 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (113331886983 / 5000000000000 : ℝ))
      (E := (cell12580 ⟨44, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (20640100113057 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (113331886983 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_45 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (16505290806557 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266641764721 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨45, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (16505290806557 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266641764721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_46 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (10311566394791 / 12500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133322885499 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨46, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (10311566394791 / 12500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133322885499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_47 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (8245863179967 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (113332487849 / 5000000000000 : ℝ))
      (E := (cell12580 ⟨47, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (8245863179967 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (113332487849 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_48 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (20606188981943 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266653779861 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨48, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (20606188981943 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266653779861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_49 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (82390903513739 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266657778823 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨49, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (82390903513739 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266657778823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_50 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (4117853726441 / 5000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133330905341 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨50, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (4117853726441 / 5000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133330905341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_51 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (8232326894441 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (17708326673 / 781250000000 : ℝ))
      (E := (cell12580 ⟨51, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (8232326894441 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (17708326673 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_52 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (5143092920753 / 6250000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266669786629 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨52, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (5143092920753 / 6250000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266669786629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_53 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (16451145572683 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (35416777881 / 1562500000000 : ℝ))
      (E := (cell12580 ⟨53, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (16451145572683 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (35416777881 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_54 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (20555498077583 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266677804479 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨54, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (20555498077583 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266677804479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_55 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41094140022381 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266681784683 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨55, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41094140022381 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266681784683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_56 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (8215459103881 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566671445171 / 25000000000000 : ℝ))
      (E := (cell12580 ⟨56, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (8215459103881 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566671445171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_57 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (82120925264717 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (90667591557 / 4000000000000 : ℝ))
      (E := (cell12580 ⟨57, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (82120925264717 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (90667591557 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_58 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41043641347433 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453338761127 / 20000000000000 : ℝ))
      (E := (cell12580 ⟨58, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41043641347433 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453338761127 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_59 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41026831650887 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566674456711 / 25000000000000 : ℝ))
      (E := (cell12580 ⟨59, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41026831650887 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566674456711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12581_40 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82696419392281 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133247232911 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨40, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82696419392281 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133247232911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_41 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82662378805163 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133249242367 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨41, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82662378805163 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133249242367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_42 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82628361880843 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (141656405587 / 6250000000000 : ℝ))
      (E := (cell12581 ⟨42, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82628361880843 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (141656405587 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_43 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82594368589537 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566626619789 / 25000000000000 : ℝ))
      (E := (cell12581 ⟨43, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82594368589537 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566626619789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_44 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41280199450807 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266510511993 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨44, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41280199450807 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266510511993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_45 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82526452787591 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133257234593 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨45, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82526452787591 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133257234593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_46 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41246265109067 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266518525999 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨46, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41246265109067 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266518525999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_47 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (10307328895507 / 12500000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266522504359 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨47, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (10307328895507 / 12500000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266522504359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_48 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41212377798159 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133263260157 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨48, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41212377798159 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133263260157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_49 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (3295636139441 / 4000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133265256523 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨49, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (3295636139441 / 4000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133265256523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_50 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82357074804429 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266534480397 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨50, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82357074804429 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266534480397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_51 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (20580817380731 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266538537989 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨51, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (20580817380731 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266538537989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_52 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82289487613051 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566635626581 / 25000000000000 : ℝ))
      (E := (cell12581 ⟨52, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82289487613051 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566635626581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_53 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (8225572904649 / 10000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266546500623 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨53, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (8225572904649 / 10000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266546500623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_54 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (10277749224383 / 12500000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266550517953 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨54, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (10277749224383 / 12500000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266550517953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_55 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41094140915369 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (226655455517 / 10000000000000 : ℝ))
      (E := (cell12581 ⟨55, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41094140915369 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (226655455517 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_56 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41077296562807 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266558549811 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨56, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41077296562807 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266558549811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_57 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82120927651937 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266562557381 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨57, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82120927651937 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266562557381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_58 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82087285382089 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266566514951 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨58, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82087285382089 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266566514951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_59 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82053666288589 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266570536843 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨59, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82053666288589 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266570536843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12582_40 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (82696416616661 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (141647951199 / 6250000000000 : ℝ))
      (E := (cell12582 ⟨40, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (82696416616661 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (141647951199 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_41 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (41331188168309 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (22663712263 / 1000000000000 : ℝ))
      (E := (cell12582 ⟨41, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (41331188168309 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (22663712263 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_42 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (82628359718949 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453275055729 / 20000000000000 : ℝ))
      (E := (cell12582 ⟨42, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (82628359718949 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453275055729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_43 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (82594366733871 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (566594814509 / 25000000000000 : ℝ))
      (E := (cell12582 ⟨43, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (82594366733871 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (566594814509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_44 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (41280198675877 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266383281197 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨44, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (41280198675877 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266383281197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_45 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (41263225771557 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266387288267 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨45, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (41263225771557 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266387288267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_46 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (4124626463931 / 5000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133195638973 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨46, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (4124626463931 / 5000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133195638973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_47 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (20614657632271 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266395248723 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨47, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (20614657632271 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266395248723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_48 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (20606188816367 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266399257791 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨48, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (20606188816367 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266399257791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_49 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (82390903458879 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (226640324433 / 10000000000000 : ℝ))
      (E := (cell12582 ⟨49, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (82390903458879 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (226640324433 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_50 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (10294634385071 / 12500000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453281453031 / 20000000000000 : ℝ))
      (E := (cell12582 ⟨50, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (10294634385071 / 12500000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453281453031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_51 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (20580817525483 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (226641125897 / 10000000000000 : ℝ))
      (E := (cell12582 ⟨51, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (20580817525483 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (226641125897 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_52 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (82289488494511 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (566603820553 / 25000000000000 : ℝ))
      (E := (cell12582 ⟨52, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (82289488494511 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (566603820553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_53 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (16451146045997 / 20000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (566604818279 / 25000000000000 : ℝ))
      (E := (cell12582 ⟨53, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (16451146045997 / 20000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (566604818279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_54 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (4111099764009 / 5000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266423287741 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨54, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (4111099764009 / 5000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266423287741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_55 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (82188283617059 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133213631929 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨55, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (82188283617059 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133213631929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_56 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (10269324401591 / 12500000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453286263253 / 20000000000000 : ℝ))
      (E := (cell12582 ⟨56, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (10269324401591 / 12500000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453286263253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_57 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (8212093003943 / 10000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266435323201 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨57, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (8212093003943 / 10000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266435323201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_58 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (82087288069549 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266439280827 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨58, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (82087288069549 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266439280827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_59 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (20513417318901 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266443303463 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨59, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (20513417318901 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266443303463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12583_40 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (10337051730243 / 12500000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566560007 / 25000000000 : ℝ))
      (E := (cell12583 ⟨40, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (10337051730243 / 12500000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566560007 / 25000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_41 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (4133118693447 / 5000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266244082139 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨41, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (4133118693447 / 5000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266244082139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_42 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20657089389471 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266248064691 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨42, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20657089389471 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266248064691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_43 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (82594364878997 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133126016873 / 50000000000000 : ℝ))
      (E := (cell12583 ⟨43, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (82594364878997 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133126016873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_44 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (82560395802647 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (283282005909 / 12500000000000 : ℝ))
      (E := (cell12583 ⟨44, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (82560395802647 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (283282005909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_45 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41263225149677 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133130022701 / 50000000000000 : ℝ))
      (E := (cell12583 ⟨45, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41263225149677 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133130022701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_46 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (16498505667957 / 20000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266264085717 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨46, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (16498505667957 / 20000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266264085717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_47 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41229314947377 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566567012243 / 25000000000000 : ℝ))
      (E := (cell12583 ⟨47, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41229314947377 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566567012243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_48 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (82424754935223 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (453254410243 / 20000000000000 : ℝ))
      (E := (cell12583 ⟨48, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (82424754935223 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (453254410243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_49 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (82390903432301 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (226627609057 / 10000000000000 : ℝ))
      (E := (cell12583 ⟨49, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (82390903432301 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (226627609057 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_50 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41178537678619 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266280105983 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨50, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41178537678619 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266280105983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_51 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41161635340717 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133142047539 / 50000000000000 : ℝ))
      (E := (cell12583 ⟨51, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41161635340717 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133142047539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_52 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (82289489376427 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266288114293 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨52, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (82289489376427 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266288114293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_53 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (822557314139 / 1000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266292101863 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨53, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (822557314139 / 1000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266292101863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_54 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41110998382839 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133148056923 / 50000000000000 : ℝ))
      (E := (cell12583 ⟨54, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41110998382839 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133148056923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_55 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (82188285403727 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (226630008801 / 10000000000000 : ℝ))
      (E := (cell12583 ⟨55, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (82188285403727 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (226630008801 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_56 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (82154597300151 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566576020011 / 25000000000000 : ℝ))
      (E := (cell12583 ⟨56, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (82154597300151 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566576020011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_57 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20530233106799 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (141644255399 / 6250000000000 : ℝ))
      (E := (cell12583 ⟨57, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20530233106799 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (141644255399 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_58 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20521822689311 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (70822253227 / 3125000000000 : ℝ))
      (E := (cell12583 ⟨58, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20521822689311 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (70822253227 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_59 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41026836131409 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (141644757919 / 6250000000000 : ℝ))
      (E := (cell12583 ⟨59, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41026836131409 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (141644757919 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12584_40 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82696411068131 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266112892269 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨40, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82696411068131 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266112892269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_41 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82662371402127 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (141632308421 / 6250000000000 : ℝ))
      (E := (cell12584 ⟨41, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82662371402127 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (141632308421 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_42 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (5164272212353 / 6250000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453224181263 / 20000000000000 : ℝ))
      (E := (cell12584 ⟨42, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (5164272212353 / 6250000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453224181263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_43 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41297181512457 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266124923903 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨43, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41297181512457 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266124923903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_44 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41280197127147 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133064463939 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨44, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41280197127147 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133064463939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_45 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (8252644905631 / 10000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453226583431 / 20000000000000 : ℝ))
      (E := (cell12584 ⟨45, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (8252644905631 / 10000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453226583431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_46 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (20623131850407 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266136890437 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨46, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (20623131850407 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266136890437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_47 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (16491725852213 / 20000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566535226277 / 25000000000000 : ℝ))
      (E := (cell12584 ⟨47, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (16491725852213 / 20000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566535226277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_48 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82424754605583 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133072450293 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨48, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82424754605583 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133072450293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_49 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (8239090340629 / 10000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266148933873 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨49, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (8239090340629 / 10000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266148933873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_50 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82357075634439 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (226615294391 / 10000000000000 : ℝ))
      (E := (cell12584 ⟨50, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82357075634439 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (226615294391 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_51 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82323271261429 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566539232081 / 25000000000000 : ℝ))
      (E := (cell12584 ⟨51, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82323271261429 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566539232081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_52 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82289490258799 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266160943551 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨52, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82289490258799 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266160943551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_53 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41127866299117 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (141635307989 / 6250000000000 : ℝ))
      (E := (cell12584 ⟨53, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41127866299117 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (141635307989 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_54 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82221998251559 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266168937203 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨54, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82221998251559 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266168937203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_55 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (4109414359537 / 5000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266172968541 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨55, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (4109414359537 / 5000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266172968541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_56 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82154599387883 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133088479687 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨56, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82154599387883 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133088479687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_57 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41060467407617 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566545241301 / 25000000000000 : ℝ))
      (E := (cell12584 ⟨57, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41060467407617 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566545241301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_58 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (10260911680647 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266184982261 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨58, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (10260911680647 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266184982261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_59 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82053675250231 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453237789477 / 20000000000000 : ℝ))
      (E := (cell12584 ⟨59, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82053675250231 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453237789477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12585_40 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82696408295221 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132992905997 / 50000000000000 : ℝ))
      (E := (cell12585 ⟨40, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82696408295221 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132992905997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_41 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (4133118446809 / 5000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226598978409 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨41, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (4133118446809 / 5000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226598978409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_42 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (516427207739 / 625000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132996901759 / 50000000000000 : ℝ))
      (E := (cell12585 ⟨42, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (516427207739 / 625000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132996901759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_43 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82594361171621 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (453199562179 / 20000000000000 : ℝ))
      (E := (cell12585 ⟨43, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82594361171621 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (453199562179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_44 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (16512078541339 / 20000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566500451339 / 25000000000000 : ℝ))
      (E := (cell12585 ⟨44, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (16512078541339 / 20000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566500451339 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_45 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41263223906991 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1133002892909 / 50000000000000 : ℝ))
      (E := (cell12585 ⟨45, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41263223906991 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1133002892909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_46 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82492526464151 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266009809859 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨46, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82492526464151 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266009809859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_47 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41229314314009 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266013817133 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨47, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41229314314009 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266013817133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_48 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82424754276547 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566504451477 / 25000000000000 : ℝ))
      (E := (cell12585 ⟨48, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82424754276547 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566504451477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_49 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41195451690423 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266021833187 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨49, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41195451690423 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266021833187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_50 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (8235707591217 / 10000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226602583791 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨50, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (8235707591217 / 10000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226602583791 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_51 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82323271841917 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (283253727213 / 12500000000000 : ℝ))
      (E := (cell12585 ⟨51, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82323271841917 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (283253727213 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_52 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (20572372785407 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566508457251 / 25000000000000 : ℝ))
      (E := (cell12585 ⟨52, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (20572372785407 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566508457251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_53 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (20563933445747 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1133018905021 / 50000000000000 : ℝ))
      (E := (cell12585 ⟨53, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (20563933445747 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1133018905021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_54 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82221999737823 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566510454219 / 25000000000000 : ℝ))
      (E := (cell12585 ⟨54, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82221999737823 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566510454219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_55 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82188288978099 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266045846363 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨55, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82188288978099 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266045846363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_56 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (20538650368981 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266049836033 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨56, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (20538650368981 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266049836033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_57 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (10265117150443 / 12500000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226605384139 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨57, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (10265117150443 / 12500000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226605384139 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_58 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82087296133343 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1133028929331 / 50000000000000 : ℝ))
      (E := (cell12585 ⟨58, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82087296133343 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1133028929331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_59 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82053678237843 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266061883873 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨59, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82053678237843 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2266061883873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12586_40 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (16539281104643 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132929364219 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨40, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (16539281104643 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132929364219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_41 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82662366471099 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265862747723 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨41, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82662366471099 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265862747723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_42 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82628351079659 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265866756303 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨42, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82628351079659 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265866756303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_43 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82594359319119 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (226587075353 / 10000000000000 : ℝ))
      (E := (cell12586 ⟨43, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82594359319119 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (226587075353 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_44 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82560391159849 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (113293736927 / 5000000000000 : ℝ))
      (E := (cell12586 ⟨44, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82560391159849 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (113293736927 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_45 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (8252644657237 / 10000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132939384551 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨45, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (8252644657237 / 10000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132939384551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_46 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (10311565690919 / 12500000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265882726233 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨46, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (10311565690919 / 12500000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265882726233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_47 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82458627995613 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132943363073 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨47, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82458627995613 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132943363073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_48 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (16484950789623 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132945383591 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨48, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (16484950789623 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132945383591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_49 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (8239090335597 / 10000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132947364783 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨49, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (8239090335597 / 10000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132947364783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_50 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82357076190431 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265898729013 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨50, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82357076190431 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265898729013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_51 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41161636211449 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (113295138161 / 5000000000000 : ℝ))
      (E := (cell12586 ⟨51, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41161636211449 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (113295138161 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_52 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82289492024913 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132953385327 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨52, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82289492024913 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132953385327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_53 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82255734968161 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132955374259 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨53, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82255734968161 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132955374259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_54 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82222001224469 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (226591475287 / 10000000000000 : ℝ))
      (E := (cell12586 ⟨54, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82222001224469 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (226591475287 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_55 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (20547072691451 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (453183756113 / 20000000000000 : ℝ))
      (E := (cell12586 ⟨55, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (20547072691451 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (453183756113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_56 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41077301782137 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132961384567 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨56, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41077301782137 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132961384567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_57 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41060469796063 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265926774079 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨57, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41060469796063 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265926774079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_58 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (16417459764349 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566482697907 / 25000000000000 : ℝ))
      (E := (cell12586 ⟨58, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (16417459764349 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566482697907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_59 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41026840612827 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566483704451 / 25000000000000 : ℝ))
      (E := (cell12586 ⟨59, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41026840612827 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566483704451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12587_40 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82696402752111 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (113286585017 / 5000000000000 : ℝ))
      (E := (cell12587 ⟨40, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82696402752111 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (113286585017 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_41 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41331182003441 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (453147141623 / 20000000000000 : ℝ))
      (E := (cell12587 ⟨41, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41331182003441 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (453147141623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_42 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82628348921907 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566434926471 / 25000000000000 : ℝ))
      (E := (cell12587 ⟨42, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82628348921907 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566434926471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_43 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82594357467407 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265743693 / 100000000000 : ℝ))
      (E := (cell12587 ⟨43, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82594357467407 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265743693 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_44 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (20640097403439 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265747727427 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨44, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (20640097403439 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265747727427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_45 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41263222665737 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566437922611 / 25000000000000 : ℝ))
      (E := (cell12587 ⟨45, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41263222665737 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566437922611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_46 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (644472848369 / 781250000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132877849217 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨46, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (644472848369 / 781250000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132877849217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_47 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (10307328420481 / 12500000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265759691049 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨47, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (10307328420481 / 12500000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265759691049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_48 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (1287886775317 / 1562500000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (56644093137 / 2500000000000 : ℝ))
      (E := (cell12587 ⟨48, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (1287886775317 / 1562500000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (56644093137 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_49 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (4119545166583 / 5000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132883870453 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨49, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (4119545166583 / 5000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132883870453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_50 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41178538234611 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132885867581 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨50, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41178538234611 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132885867581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_51 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (20580818251093 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566443926469 / 25000000000000 : ℝ))
      (E := (cell12587 ⟨51, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (20580818251093 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566443926469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_52 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41144746454327 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132889854741 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨52, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41144746454327 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132889854741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_53 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82255736153753 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566445935813 / 25000000000000 : ℝ))
      (E := (cell12587 ⟨53, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82255736153753 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566445935813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_54 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82222002711497 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (70805867037 / 3125000000000 : ℝ))
      (E := (cell12587 ⟨54, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82222002711497 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (70805867037 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_55 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (16437658510771 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265791771147 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨55, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (16437658510771 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265791771147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_56 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82154605652933 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566448939669 / 25000000000000 : ℝ))
      (E := (cell12587 ⟨56, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82154605652933 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566448939669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_57 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82120941980981 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265799763269 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨57, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82120941980981 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265799763269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_58 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82087301510383 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265803781157 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨58, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82087301510383 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265803781157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_59 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (16410736842733 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132903874587 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨59, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (16410736842733 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132903874587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12588_40 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82696399981909 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265604727701 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨40, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82696399981909 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265604727701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_41 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82662361543531 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265608724027 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨41, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82662361543531 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265608724027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_42 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (41314173382491 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265612711047 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨42, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (41314173382491 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265612711047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_43 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (41297177808243 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265616746921 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨43, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (41297177808243 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265616746921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_44 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (16512077613683 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226562071319 / 10000000000000 : ℝ))
      (E := (cell12588 ⟨44, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (16512077613683 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226562071319 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_45 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82526444091293 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265624726407 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨45, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82526444091293 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265624726407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_46 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (8249252365579 / 10000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (35400448851 / 1562500000000 : ℝ))
      (E := (cell12588 ⟨46, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (8249252365579 / 10000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (35400448851 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_47 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (3298345069309 / 4000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132816355921 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨47, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (3298345069309 / 4000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132816355921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_48 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (10303094161633 / 12500000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566409184933 / 25000000000000 : ℝ))
      (E := (cell12588 ⟨48, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (10303094161633 / 12500000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566409184933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_49 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82390903307917 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265640749311 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨49, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82390903307917 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265640749311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_50 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (41178538374271 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132822369207 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨50, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (41178538374271 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132822369207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_51 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (41161636793169 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (453129752733 / 20000000000000 : ℝ))
      (E := (cell12588 ⟨51, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (41161636793169 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (453129752733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_52 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (1645789875857 / 2000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265652763527 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨52, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (1645789875857 / 2000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265652763527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_53 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (20563934334941 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265656735203 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨53, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (20563934334941 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265656735203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_54 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (20555501049727 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265660734751 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨54, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (20555501049727 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265660734751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_55 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (328753177369 / 400000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265664759023 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨55, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (328753177369 / 400000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265664759023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_56 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (821546077419 / 1000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265668745549 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨56, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (821546077419 / 1000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265668745549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_57 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82120944370107 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566418187457 / 25000000000000 : ℝ))
      (E := (cell12588 ⟨57, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82120944370107 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566418187457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_58 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82087304199257 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226567676809 / 10000000000000 : ℝ))
      (E := (cell12588 ⟨58, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82087304199257 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226567676809 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_59 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (41026843600937 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132840398177 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨59, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (41026843600937 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132840398177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12589_40 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (8269639721261 / 10000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (283184718973 / 12500000000000 : ℝ))
      (E := (cell12589 ⟨40, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (8269639721261 / 10000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (283184718973 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_41 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (20665589770261 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (113274089773 / 5000000000000 : ℝ))
      (E := (cell12589 ⟨41, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (20665589770261 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (113274089773 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_42 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (20657086152221 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132742885897 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨42, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (20657086152221 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132742885897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_43 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41297176883177 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (28318622471 / 1250000000000 : ℝ))
      (E := (cell12589 ⟨43, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41297176883177 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (28318622471 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_44 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82560386523827 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (226549381349 / 10000000000000 : ℝ))
      (E := (cell12589 ⟨44, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82560386523827 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (226549381349 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_45 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82526442851827 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (453099551857 / 20000000000000 : ℝ))
      (E := (cell12589 ⟨45, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82526442851827 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (453099551857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_46 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (3299700908841 / 4000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (90620072413 / 4000000000000 : ℝ))
      (E := (cell12589 ⟨46, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (3299700908841 / 4000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (90620072413 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_47 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41229313051121 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265505788527 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨47, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41229313051121 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265505788527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_48 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82424752966443 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132754904969 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨48, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82424752966443 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132754904969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_49 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82390903284741 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (226551381373 / 10000000000000 : ℝ))
      (E := (cell12589 ⟨49, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82390903284741 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (226551381373 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_50 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (10294634628549 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265517797743 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨50, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (10294634628549 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265517797743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_51 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41161637084399 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (453104363719 / 20000000000000 : ℝ))
      (E := (cell12589 ⟨51, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41161637084399 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (453104363719 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_52 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41144747338751 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265525814753 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨52, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41144747338751 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265525814753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_53 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82255738526193 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132764921229 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨53, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82255738526193 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132764921229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_54 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (822220056867 / 1000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265533839707 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨54, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (822220056867 / 1000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265533839707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_55 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82188296130991 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265537803281 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨55, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82188296130991 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265537803281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_56 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (10269326228897 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132770923989 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨56, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (10269326228897 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132770923989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_57 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (16424189351901 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265545852029 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨57, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (16424189351901 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265545852029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_58 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (16417461377673 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (226554981159 / 10000000000000 : ℝ))
      (E := (cell12589 ⟨58, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (16417461377673 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (226554981159 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_59 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82053690190281 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265553840979 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨59, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82053690190281 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265553840979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12590_40 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82696394444213 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (141584430629 / 6250000000000 : ℝ))
      (E := (cell12590 ⟨40, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82696394444213 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (141584430629 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_41 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41331178309711 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (283169357957 / 12500000000000 : ℝ))
      (E := (cell12590 ⟨41, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41331178309711 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (283169357957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_42 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82628342453613 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132679444063 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨42, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82628342453613 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132679444063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_43 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82594351917011 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132681452043 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨43, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82594351917011 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132681452043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_44 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82560384979991 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265366910669 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨44, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82560384979991 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265366910669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_45 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20631610403269 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265370906787 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨45, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20631610403269 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265370906787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_46 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82492521786939 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265374891139 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨46, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82492521786939 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265374891139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_47 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (206146563681 / 250000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132689460553 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨47, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (206146563681 / 250000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132689460553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_48 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41212376320213 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132691438587 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨48, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41212376320213 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132691438587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_49 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82390903262131 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132693437609 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨49, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82390903262131 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132693437609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_50 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82357077308771 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (45307818263 / 2000000000000 : ℝ))
      (E := (cell12590 ⟨50, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82357077308771 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (45307818263 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_51 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82323274751749 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453078985933 / 20000000000000 : ℝ))
      (E := (cell12590 ⟨51, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82323274751749 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453078985933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_52 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (8228949556261 / 10000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132699461089 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨52, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (8228949556261 / 10000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132699461089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_53 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82255739713041 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (226540288789 / 10000000000000 : ℝ))
      (E := (cell12590 ⟨53, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82255739713041 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (226540288789 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_54 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82222007174873 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265406941921 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨54, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82222007174873 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265406941921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_55 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20547074480019 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566352725981 / 25000000000000 : ℝ))
      (E := (cell12590 ⟨55, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20547074480019 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566352725981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_56 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (2053865298019 / 2500000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (113270747387 / 5000000000000 : ℝ))
      (E := (cell12590 ⟨56, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (2053865298019 / 2500000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (113270747387 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_57 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (3284837965967 / 4000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265418951599 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨57, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (3284837965967 / 4000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265418951599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_58 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20521827394427 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265422911659 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨58, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20521827394427 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265422911659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_59 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82053693178887 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (283178367779 / 12500000000000 : ℝ))
      (E := (cell12590 ⟨59, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82053693178887 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (283178367779 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12591_40 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82696391676717 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (226522402507 / 10000000000000 : ℝ))
      (E := (cell12591 ⟨40, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82696391676717 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (226522402507 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_41 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (10332794269833 / 12500000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (283153505767 / 12500000000000 : ℝ))
      (E := (cell12591 ⟨41, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (10332794269833 / 12500000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (283153505767 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_42 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82628340299169 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265232001259 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨42, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82628340299169 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265232001259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_43 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41297175034229 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566309001833 / 25000000000000 : ℝ))
      (E := (cell12591 ⟨43, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41297175034229 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566309001833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_44 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82560383436907 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (90609600189 / 4000000000000 : ℝ))
      (E := (cell12591 ⟨44, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82560383436907 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (90609600189 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_45 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82526440375039 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265244051207 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨45, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82526440375039 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265244051207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_46 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82492520853529 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265248027787 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨46, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82492520853529 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265248027787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_47 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41229312421599 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265252050677 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨47, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41229312421599 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265252050677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_48 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20606188078753 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (226525605929 / 10000000000000 : ℝ))
      (E := (cell12591 ⟨48, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20606188078753 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (226525605929 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_49 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82390903240087 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (283157506459 / 12500000000000 : ℝ))
      (E := (cell12591 ⟨49, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82390903240087 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (283157506459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_50 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82357077589679 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265264025663 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨50, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82357077589679 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265264025663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_51 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (10290409416899 / 12500000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265268037881 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨51, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (10290409416899 / 12500000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265268037881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_52 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20572374112043 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265272026787 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨52, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20572374112043 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265272026787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_53 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20563935225077 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132638024313 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨53, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20563935225077 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132638024313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_54 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82222008663429 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265280041391 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨54, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82222008663429 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265280041391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_55 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82188299709507 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265284060951 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨55, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82188299709507 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265284060951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_56 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20538653502663 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (453057608967 / 20000000000000 : ℝ))
      (E := (cell12591 ⟨56, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20538653502663 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (453057608967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_57 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20530237884779 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265292048541 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨57, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20530237884779 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265292048541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_58 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82087312267287 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132648034147 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨58, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82087312267287 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132648034147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_59 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82053696167691 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132650050057 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨59, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82053696167691 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132650050057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12592_40 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (82696388910123 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132548607769 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨40, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (82696388910123 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132548607769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_41 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (8266235169877 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (113255061269 / 5000000000000 : ℝ))
      (E := (cell12592 ⟨41, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (8266235169877 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (113255061269 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_42 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (5164271134097 / 6250000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132552614381 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨42, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (5164271134097 / 6250000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132552614381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_43 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41297174110347 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265109225033 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨43, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41297174110347 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265109225033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_44 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41280190947287 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265113213323 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨44, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41280190947287 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265113213323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_45 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (82526439137717 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265117192543 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨45, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (82526439137717 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265117192543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_46 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (82492519920797 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265121220267 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨46, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (82492519920797 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265121220267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_47 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (20614656053659 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265125236143 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨47, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (20614656053659 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265125236143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_48 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (82424751990201 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265129238437 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨48, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (82424751990201 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265129238437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_49 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (5149431451163 / 6250000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (566283306299 / 25000000000000 : ℝ))
      (E := (cell12592 ⟨49, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (5149431451163 / 6250000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (566283306299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_50 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (20589269467779 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265137253227 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨50, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (20589269467779 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265137253227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_51 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (10290409489891 / 12500000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453028240447 / 20000000000000 : ℝ))
      (E := (cell12592 ⟨51, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (10290409489891 / 12500000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453028240447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_52 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (8228949733419 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (283143155827 / 12500000000000 : ℝ))
      (E := (cell12592 ⟨52, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (8228949733419 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (283143155827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_53 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (10281967760999 / 12500000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132574632813 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨53, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (10281967760999 / 12500000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132574632813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_54 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41111005076183 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265153256251 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨54, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41111005076183 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265153256251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_55 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41094150749641 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132578607637 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨55, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41094150749641 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132578607637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_56 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (20538654025213 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265161257489 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨56, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (20538654025213 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265161257489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_57 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (5132559620583 / 6250000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132582630563 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨57, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (5132559620583 / 6250000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132582630563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_58 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (820873149571 / 1000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132584640749 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨58, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (820873149571 / 1000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132584640749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_59 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41026849578347 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265173255441 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨59, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41026849578347 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265173255441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12593_40 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (8269638614443 / 10000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566242600683 / 25000000000000 : ℝ))
      (E := (cell12593 ⟨40, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (8269638614443 / 10000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566242600683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_41 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (82662349239739 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264974401389 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨41, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (82662349239739 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264974401389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_42 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (2065708399819 / 2500000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264978453069 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨42, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (2065708399819 / 2500000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264978453069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_43 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (82594346373719 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (283122804947 / 12500000000000 : ℝ))
      (E := (cell12593 ⟨43, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (82594346373719 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (283122804947 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_44 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41280190176497 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264986418799 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨44, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41280190176497 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264986418799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_45 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (8252643790111 / 10000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (452998089701 / 20000000000000 : ℝ))
      (E := (cell12593 ⟨45, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (8252643790111 / 10000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (452998089701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_46 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41246259494371 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264994409703 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨46, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41246259494371 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264994409703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_47 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41229311793357 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566249604651 / 25000000000000 : ℝ))
      (E := (cell12593 ⟨47, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41229311793357 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566249604651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_48 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (82424751665993 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (283125301827 / 12500000000000 : ℝ))
      (E := (cell12593 ⟨48, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (82424751665993 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (283125301827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_49 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20114966601 / 24414062500 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265006454737 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨49, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20114966601 / 24414062500 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265006454737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_50 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41178539076541 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (22650104779 / 1000000000000 : ℝ))
      (E := (cell12593 ⟨50, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41178539076541 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (22650104779 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_51 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (16464655300711 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265014481727 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨51, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (16464655300711 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265014481727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_52 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41144749110331 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (226501846363 / 10000000000000 : ℝ))
      (E := (cell12593 ⟨52, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41144749110331 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (226501846363 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_53 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (16451148655219 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265022479847 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨53, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (16451148655219 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265022479847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_54 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20555502910421 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566256617093 / 25000000000000 : ℝ))
      (E := (cell12593 ⟨54, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20555502910421 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566256617093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_55 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (82188303289401 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132515242537 / 50000000000000 : ℝ))
      (E := (cell12593 ⟨55, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (82188303289401 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132515242537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_56 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (32091647731 / 39062500000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132517233739 / 50000000000000 : ℝ))
      (E := (cell12593 ⟨56, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (32091647731 / 39062500000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132517233739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_57 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20530239079953 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265038471083 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨57, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20530239079953 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265038471083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_58 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20521829411787 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (141565155757 / 6250000000000 : ℝ))
      (E := (cell12593 ⟨58, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20521829411787 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (141565155757 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_59 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (16410740429179 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265046467399 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨59, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (16410740429179 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2265046467399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12594_40 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82696383379637 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264843704129 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨40, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82696383379637 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264843704129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_41 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20665586695393 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (452969538337 / 20000000000000 : ℝ))
      (E := (cell12594 ⟨41, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20665586695393 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (452969538337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_42 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (41314166920397 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264851674181 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨42, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (41314166920397 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264851674181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_43 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82594344527533 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264855709769 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨43, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82594344527533 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264855709769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_44 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20640094703041 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566214919997 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨44, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20640094703041 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566214919997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_45 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (644737786447 / 781250000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566215925347 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨45, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (644737786447 / 781250000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566215925347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_46 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20623129514341 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264867713853 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨46, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20623129514341 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264867713853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_47 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82458622959431 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264871715863 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨47, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82458622959431 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264871715863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_48 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82424751342387 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (28310946321 / 1250000000000 : ℝ))
      (E := (cell12594 ⟨48, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82424751342387 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (28310946321 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_49 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82390903177349 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264879740299 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨49, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82390903177349 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264879740299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_50 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (10294634804447 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132441849841 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨50, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (10294634804447 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132441849841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_51 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82323277088473 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566221924843 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨51, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82323277088473 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566221924843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_52 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82289499107589 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264891736847 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨52, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82289499107589 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264891736847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_53 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (16451148892923 / 20000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132447875167 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨53, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (16451148892923 / 20000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132447875167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_54 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (41111006565691 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (113244986841 / 5000000000000 : ℝ))
      (E := (cell12594 ⟨54, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (41111006565691 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (113244986841 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_55 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (16437661015973 / 20000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566225938043 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨55, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (16437661015973 / 20000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566225938043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_56 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (3286184811287 / 4000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264907733917 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨56, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (3286184811287 / 4000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264907733917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_57 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82120958710567 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (45298234751 / 2000000000000 : ℝ))
      (E := (cell12594 ⟨57, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82120958710567 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (45298234751 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_58 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (8208732033743 / 10000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264915759297 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨58, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (8208732033743 / 10000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264915759297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_59 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82053705135293 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (226491973599 / 10000000000000 : ℝ))
      (E := (cell12594 ⟨59, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82053705135293 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (226491973599 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12595_40 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (16539276123149 / 20000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452943400451 / 20000000000000 : ℝ))
      (E := (cell12595 ⟨40, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (16539276123149 / 20000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452943400451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_41 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (20665586081067 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264720978749 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨41, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (20665586081067 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264720978749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_42 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (16525666337931 / 20000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452945001933 / 20000000000000 : ℝ))
      (E := (cell12595 ⟨42, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (16525666337931 / 20000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452945001933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_43 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41297171341067 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264728976807 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨43, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41297171341067 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264728976807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_44 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (16512075454417 / 20000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264732996891 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨44, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (16512075454417 / 20000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264732996891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_45 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (20631608857509 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452947402009 / 20000000000000 : ℝ))
      (E := (cell12595 ⟨45, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (20631608857509 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452947402009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_46 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41246258563331 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132370507481 / 50000000000000 : ℝ))
      (E := (cell12595 ⟨46, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41246258563331 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132370507481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_47 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (20614655583197 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264745010119 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨47, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (20614655583197 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264745010119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_48 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (10303093877423 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264748993777 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨48, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (10303093877423 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264748993777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_49 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (82390903157567 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132376511467 / 50000000000000 : ℝ))
      (E := (cell12595 ⟨49, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (82390903157567 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132376511467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_50 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41178539359299 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264757036519 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨50, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41178539359299 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264757036519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_51 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (82323277673883 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452952206431 / 20000000000000 : ℝ))
      (E := (cell12595 ⟨51, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (82323277673883 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452952206431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_52 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (82289499994971 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (9059060029 / 400000000000 : ℝ))
      (E := (cell12595 ⟨52, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (82289499994971 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (9059060029 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_53 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (82255745653553 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566192254511 / 25000000000000 : ℝ))
      (E := (cell12595 ⟨53, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (82255745653553 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566192254511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_54 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41111007310731 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132386530797 / 50000000000000 : ℝ))
      (E := (cell12595 ⟨54, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41111007310731 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132386530797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_55 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (82188306870673 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (283097127071 / 12500000000000 : ℝ))
      (E := (cell12595 ⟨55, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (82188306870673 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (283097127071 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_56 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41077311186649 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452956211361 / 20000000000000 : ℝ))
      (E := (cell12595 ⟨56, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41077311186649 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452956211361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_57 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (10265120137699 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264785060529 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨57, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (10265120137699 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264785060529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_58 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (82087323027947 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264789023893 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨58, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (82087323027947 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264789023893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_59 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (8205370812489 / 10000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566198265303 / 25000000000000 : ℝ))
      (E := (cell12595 ⟨59, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (8205370812489 / 10000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566198265303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12596_40 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41348188926377 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132295177923 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨40, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41348188926377 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132295177923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_41 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82662341867827 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (113229716067 / 5000000000000 : ℝ))
      (E := (cell12596 ⟨41, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82662341867827 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (113229716067 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_42 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (4131416476967 / 5000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264598341957 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨42, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (4131416476967 / 5000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264598341957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_43 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (20648585209381 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264602358303 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨43, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (20648585209381 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264602358303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_44 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82560375732757 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264606369507 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨44, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82560375732757 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264606369507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_45 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82526434195569 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132305187239 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨45, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82526434195569 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132305187239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_46 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (20623129049159 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566153592977 / 25000000000000 : ℝ))
      (E := (cell12596 ⟨46, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (20623129049159 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566153592977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_47 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (2576831928337 / 3125000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264618360273 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨47, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (2576831928337 / 3125000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264618360273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_48 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82424750696983 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452924467567 / 20000000000000 : ℝ))
      (E := (cell12596 ⟨48, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82424750696983 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452924467567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_49 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (1647818062767 / 2000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264626361589 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨49, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (1647818062767 / 2000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264626361589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_50 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82357079002149 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132315185233 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨50, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82357079002149 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132315185233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_51 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (10290409782473 / 12500000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264634362087 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨51, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (10290409782473 / 12500000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264634362087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_52 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82289500882807 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132319196439 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨52, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82289500882807 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132319196439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_53 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (20563936710727 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (283080300133 / 12500000000000 : ℝ))
      (E := (cell12596 ⟨53, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (20563936710727 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (283080300133 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_54 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82222016111923 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (226464638363 / 10000000000000 : ℝ))
      (E := (cell12596 ⟨54, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82222016111923 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (226464638363 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_55 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (3287532346473 / 4000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264650396443 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨55, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (3287532346473 / 4000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264650396443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_56 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82154624464729 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566163594257 / 25000000000000 : ℝ))
      (E := (cell12596 ⟨56, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82154624464729 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566163594257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_57 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82120963492889 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (28308229761 / 1250000000000 : ℝ))
      (E := (cell12596 ⟨57, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82120963492889 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (28308229761 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_58 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82087325718697 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132331202111 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨58, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82087325718697 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132331202111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_59 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (20513427778671 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566166595971 / 25000000000000 : ℝ))
      (E := (cell12596 ⟨59, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (20513427778671 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566166595971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12597_40 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82696375090663 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264463706169 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨40, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82696375090663 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264463706169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_41 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (10332792426531 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132233859731 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨41, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (10332792426531 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132233859731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_42 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82628327389851 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (28305896623 / 1250000000000 : ℝ))
      (E := (cell12597 ⟨42, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82628327389851 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (28305896623 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_43 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41297169496851 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132237868323 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨43, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41297169496851 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132237868323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_44 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (4128018709709 / 5000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (17691247961 / 781250000000 : ℝ))
      (E := (cell12597 ⟨44, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (4128018709709 / 5000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (17691247961 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_45 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (10315804120227 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264483735833 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨45, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (10315804120227 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264483735833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_46 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82492515267287 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132243862907 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨46, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82492515267287 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132243862907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_47 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82458621081419 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264491766327 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨47, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82458621081419 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264491766327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_48 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82424750375183 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452899147571 / 20000000000000 : ℝ))
      (E := (cell12597 ⟨48, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82424750375183 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452899147571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_49 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41195451559849 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264499756269 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨49, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41195451559849 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264499756269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_50 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82357079286227 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264503760499 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨50, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82357079286227 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264503760499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_51 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (2572602463943 / 3125000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452901549633 / 20000000000000 : ℝ))
      (E := (cell12597 ⟨51, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (2572602463943 / 3125000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452901549633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_52 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82289501771097 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132255887847 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨52, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82289501771097 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132255887847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_53 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82255748032681 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264515781309 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨53, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82255748032681 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264515781309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_54 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (20555504400691 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (566129940499 / 25000000000000 : ℝ))
      (E := (cell12597 ⟨54, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (20555504400691 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (566129940499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_55 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82188310453321 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264523773619 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨55, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82188310453321 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264523773619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_56 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41077313278233 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452905550741 / 20000000000000 : ℝ))
      (E := (cell12597 ⟨56, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41077313278233 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452905550741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_57 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (10265120735557 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452906351549 / 20000000000000 : ℝ))
      (E := (cell12597 ⟨57, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (10265120735557 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452906351549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_58 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41043664204841 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (566133945491 / 25000000000000 : ℝ))
      (E := (cell12597 ⟨58, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41043664204841 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (566133945491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_59 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (20513428526169 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (226453976319 / 10000000000000 : ℝ))
      (E := (cell12597 ⟨59, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (20513428526169 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (226453976319 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12598_40 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82696372329471 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264337170699 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨40, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82696372329471 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264337170699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_41 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (20665584239383 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452868234623 / 20000000000000 : ℝ))
      (E := (cell12598 ⟨41, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (20665584239383 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452868234623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_42 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (41314162620593 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566086293329 / 25000000000000 : ℝ))
      (E := (cell12598 ⟨42, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (41314162620593 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566086293329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_43 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82594337150667 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264349170643 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨43, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82594337150667 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264349170643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_44 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82560372656353 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (35380518191 / 1562500000000 : ℝ))
      (E := (cell12598 ⟨44, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82560372656353 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (35380518191 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_45 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (10315803966097 / 12500000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132178576483 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨45, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (10315803966097 / 12500000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132178576483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_46 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (41246257169307 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264361194437 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨46, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (41246257169307 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264361194437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_47 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (20614655114173 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132182584691 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨47, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (20614655114173 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132182584691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_48 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (16484950010797 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132184596919 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨48, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (16484950010797 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132184596919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_49 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82390903101611 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566093301743 / 25000000000000 : ℝ))
      (E := (cell12598 ⟨49, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82390903101611 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566093301743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_50 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82357079570833 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264377206617 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨50, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82357079570833 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264377206617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_51 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82323279433059 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (226438119039 / 10000000000000 : ℝ))
      (E := (cell12598 ⟨51, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82323279433059 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (226438119039 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_52 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82289502659841 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132192607359 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨52, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82289502659841 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132192607359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_53 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82255749222871 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (70762163057 / 3125000000000 : ℝ))
      (E := (cell12598 ⟨53, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82255749222871 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (70762163057 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_54 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (41111009546993 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566098299173 / 25000000000000 : ℝ))
      (E := (cell12598 ⟨54, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (41111009546993 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566098299173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_55 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (2054707806129 / 2500000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566099301797 / 25000000000000 : ℝ))
      (E := (cell12598 ⟨55, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (2054707806129 / 2500000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566099301797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_56 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82154628648511 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264401186833 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨56, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82154628648511 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264401186833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_57 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82120968276293 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566101297781 / 25000000000000 : ℝ))
      (E := (cell12598 ⟨57, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82120968276293 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566101297781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_58 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82087331100901 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (56610230407 / 2500000000000 : ℝ))
      (E := (cell12598 ⟨58, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82087331100901 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (56610230407 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_59 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (16410743418973 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566103299783 / 25000000000000 : ℝ))
      (E := (cell12598 ⟨59, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (16410743418973 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566103299783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12599_40 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82696369569179 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (56605265799 / 2500000000000 : ℝ))
      (E := (cell12599 ⟨40, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82696369569179 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (56605265799 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_41 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82662334503677 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (113210731177 / 5000000000000 : ℝ))
      (E := (cell12599 ⟨41, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82662334503677 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (113210731177 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_42 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82628323093347 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264218613601 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨42, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82628323093347 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264218613601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_43 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82594335308419 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264222660297 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨43, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82594335308419 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264222660297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_44 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (20640092779819 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132113322579 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨44, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (20640092779819 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132113322579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_45 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (1289475476507 / 1562500000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132115312939 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨45, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (1289475476507 / 1562500000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132115312939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_46 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (10311564176327 / 12500000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (283029332503 / 12500000000000 : ℝ))
      (E := (cell12599 ⟨46, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (10311564176327 / 12500000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (283029332503 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_47 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (16491723966521 / 20000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264238628337 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨47, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (16491723966521 / 20000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264238628337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_48 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82424749733389 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132121323429 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨48, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82424749733389 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132121323429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_49 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (10298862885511 / 12500000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264246654751 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨49, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (10298862885511 / 12500000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264246654751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_50 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82357079855967 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264250649847 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨50, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82357079855967 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264250649847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_51 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82323280020433 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132127314883 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨51, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82323280020433 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132127314883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_52 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41144751774519 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566064662733 / 25000000000000 : ℝ))
      (E := (cell12599 ⟨52, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41144751774519 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566064662733 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_53 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41127875206739 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132131325783 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨53, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41127875206739 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132131325783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_54 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82222020585587 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (56606667193 / 2500000000000 : ℝ))
      (E := (cell12599 ⟨54, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82222020585587 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (56606667193 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_55 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82188314037343 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566067674287 / 25000000000000 : ℝ))
      (E := (cell12599 ⟨55, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82188314037343 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566067674287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_56 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82154630740863 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452854935283 / 20000000000000 : ℝ))
      (E := (cell12599 ⟨56, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82154630740863 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452854935283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_57 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82120970668401 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264278681017 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨57, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82120970668401 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264278681017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_58 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41043666896177 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566070676793 / 25000000000000 : ℝ))
      (E := (cell12599 ⟨58, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41043666896177 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566070676793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_59 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (20513430021313 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (226428669171 / 10000000000000 : ℝ))
      (E := (cell12599 ⟨59, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (20513430021313 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (226428669171 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

end BstLean.Part268
