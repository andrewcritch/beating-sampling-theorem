import BstLean.Part268CellShard9Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12575_20 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (41691150818247 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (113358938817 / 5000000000000 : ℝ))
      (E := (cell12575 ⟨20, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (41691150818247 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (113358938817 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_21 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (5209236212769 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133591374929 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨21, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (5209236212769 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133591374929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_22 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83313281466203 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267186786479 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨22, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83313281466203 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267186786479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_23 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83278807789199 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267190773593 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨23, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83278807789199 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267190773593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_24 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83244358340469 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267194773247 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨24, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83244358340469 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267194773247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_25 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (130015520449 / 156250000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267198788959 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨25, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (130015520449 / 156250000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267198788959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_26 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (16635106399477 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267202765609 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨26, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (16635106399477 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267202765609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_27 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (5196322189889 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (35425105697 / 1562500000000 : ℝ))
      (E := (cell12575 ⟨27, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (5196322189889 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (35425105697 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_28 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (20776700544431 / 25000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267210788773 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨28, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (20776700544431 / 25000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267210788773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_29 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83072473383897 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267214782211 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨29, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83072473383897 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267214782211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_30 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (16607633724983 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (283402343401 / 12500000000000 : ℝ))
      (E := (cell12575 ⟨30, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (16607633724983 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (283402343401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_31 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (20750971967279 / 25000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (113361137217 / 5000000000000 : ℝ))
      (E := (cell12575 ⟨31, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (20750971967279 / 25000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (113361137217 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_32 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82969631084999 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133613387751 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨32, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82969631084999 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133613387751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_33 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82935398241223 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (226723078379 / 10000000000000 : ℝ))
      (E := (cell12575 ⟨33, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82935398241223 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (226723078379 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_34 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (5181324331663 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (226723477057 / 10000000000000 : ℝ))
      (E := (cell12575 ⟨34, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (5181324331663 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (226723477057 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_35 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82867004250129 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566809698901 / 25000000000000 : ℝ))
      (E := (cell12575 ⟨35, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82867004250129 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566809698901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_36 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (82832843040923 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267242801237 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨36, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (82832843040923 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267242801237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_37 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (41399352824141 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133623394079 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨37, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (41399352824141 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133623394079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_38 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (41382296020827 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566812689209 / 25000000000000 : ℝ))
      (E := (cell12575 ⟨38, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (41382296020827 / 50000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566812689209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_39 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (1034131277383 / 1250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566813691557 / 25000000000000 : ℝ))
      (E := (cell12575 ⟨39, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (1034131277383 / 1250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566813691557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12576_20 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (10422786577381 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (226705129733 / 10000000000000 : ℝ))
      (E := (cell12576 ⟨20, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (10422786577381 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (226705129733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_21 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83347770702819 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267055302679 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨21, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83347770702819 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267055302679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_22 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41656636540119 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566764813817 / 25000000000000 : ℝ))
      (E := (cell12576 ⟨22, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41656636540119 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566764813817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_23 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41639399859157 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566765818923 / 25000000000000 : ℝ))
      (E := (cell12576 ⟨23, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41639399859157 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566765818923 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_24 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (3329774023369 / 4000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267067251057 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨24, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (3329774023369 / 4000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267067251057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_25 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83209925645317 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267071301579 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨25, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83209925645317 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267071301579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_26 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83175524869107 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (226707525539 / 10000000000000 : ℝ))
      (E := (cell12576 ⟨26, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83175524869107 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (226707525539 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_27 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41570574111637 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267079290693 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨27, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41570574111637 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267079290693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_28 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41553397837833 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267083293467 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨28, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41553397837833 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267083293467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_29 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (16614493438859 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (90683490649 / 4000000000000 : ℝ))
      (E := (cell12576 ⟨29, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (16614493438859 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (90683490649 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_30 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (10379770343417 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267091269751 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨30, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (10379770343417 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267091269751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_31 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83003882303127 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267095306169 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨31, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83003882303127 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267095306169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_32 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (82969625830167 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566774815069 / 25000000000000 : ℝ))
      (E := (cell12576 ⟨32, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (82969625830167 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566774815069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_33 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (20733848324279 / 25000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (4427936151 / 195312500000 : ℝ))
      (E := (cell12576 ⟨33, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (20733848324279 / 25000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (4427936151 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_34 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (16580236934559 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267107279 / 100000000000 : ℝ))
      (E := (cell12576 ⟨34, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (16580236934559 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267107279 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_35 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (4143349996309 / 5000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (70847227739 / 3125000000000 : ℝ))
      (E := (cell12576 ⟨35, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (4143349996309 / 5000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (70847227739 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_36 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (8283283902641 / 10000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267115277597 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨36, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (8283283902641 / 10000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267115277597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_37 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (10349837742847 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (453423861641 / 20000000000000 : ℝ))
      (E := (cell12576 ⟨37, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (10349837742847 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (453423861641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_38 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41382294322363 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267123262633 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨38, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41382294322363 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267123262633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_39 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (16546099820373 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566781829297 / 25000000000000 : ℝ))
      (E := (cell12576 ⟨39, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (16546099820373 / 20000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566781829297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12577_20 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (10422785450409 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266923814247 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨20, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (10422785450409 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266923814247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_21 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (16669552400593 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266927851467 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨21, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (16669552400593 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266927851467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_22 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41656632347933 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266931836689 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨22, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41656632347933 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266931836689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_23 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83278791648983 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266935832173 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨23, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83278791648983 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266935832173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_24 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (16648868565899 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266939841673 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨24, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (16648868565899 / 20000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266939841673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_25 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83209918204751 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266943810323 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨25, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83209918204751 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266943810323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_26 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41587758871133 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266947858151 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨26, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41587758871133 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266947858151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_27 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83141141409723 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266951812983 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨27, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83141141409723 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266951812983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_28 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83106789174969 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133477926429 / 50000000000000 : ℝ))
      (E := (cell12577 ⟨28, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83106789174969 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133477926429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_29 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (1298007203219 / 1562500000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266959804999 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨29, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (1298007203219 / 1562500000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266959804999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_30 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41519078435521 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266963847117 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨30, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41519078435521 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266963847117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_31 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (5187742296149 / 6250000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453393561167 / 20000000000000 : ℝ))
      (E := (cell12577 ⟨31, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (5187742296149 / 6250000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453393561167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_32 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41484810288271 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566742964637 / 25000000000000 : ℝ))
      (E := (cell12577 ⟨32, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41484810288271 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566742964637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_33 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82935388354179 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (90679033251 / 4000000000000 : ℝ))
      (E := (cell12577 ⟨33, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82935388354179 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (90679033251 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_34 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41450590020057 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266979842503 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨34, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41450590020057 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266979842503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_35 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41433497801663 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133491917413 / 50000000000000 : ℝ))
      (E := (cell12577 ⟨35, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41433497801663 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133491917413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_36 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82832835012953 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266987867797 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨36, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82832835012953 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266987867797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_37 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82798698238287 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266991824849 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨37, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82798698238287 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266991824849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_38 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82764585248779 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266995823753 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨38, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82764585248779 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266995823753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_39 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (82730496014033 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266999864821 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨39, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (82730496014033 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266999864821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12578_20 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (16676454917833 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (18134371549 / 800000000000 : ℝ))
      (E := (cell12578 ⟨20, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (16676454917833 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (18134371549 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_21 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41673876652371 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (141675028407 / 6250000000000 : ℝ))
      (E := (cell12578 ⟨21, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41673876652371 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (141675028407 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_22 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (16662651262617 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266804414119 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨22, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (16662651262617 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266804414119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_23 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (20819695895301 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266808443039 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨23, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (20819695895301 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266808443039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_24 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (2081108376907 / 2500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283351553547 / 12500000000000 : ℝ))
      (E := (cell12578 ⟨24, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (2081108376907 / 2500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283351553547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_25 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (83209910765661 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (56670410799 / 2500000000000 : ℝ))
      (E := (cell12578 ⟨25, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (83209910765661 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (56670410799 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_26 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (2599234706777 / 3125000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566705099667 / 25000000000000 : ℝ))
      (E := (cell12578 ⟨26, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (2599234706777 / 3125000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566705099667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_27 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (83141134597571 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133412224169 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨27, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (83141134597571 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133412224169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_28 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (5194173917227 / 6250000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133414204247 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨28, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (5194173917227 / 6250000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133414204247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_29 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (4153622740953 / 5000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (226683245701 / 10000000000000 : ℝ))
      (E := (cell12578 ⟨29, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (4153622740953 / 5000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (226683245701 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_30 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (1297471109313 / 1562500000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133418210403 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨30, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (1297471109313 / 1562500000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133418210403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_31 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (83003871174887 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266840418911 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨31, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (83003871174887 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266840418911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_32 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41484807662063 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266844453219 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨32, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41484807662063 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266844453219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_33 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (20733845853103 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283356051031 / 12500000000000 : ℝ))
      (E := (cell12578 ⟨33, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (20733845853103 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283356051031 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_34 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (16580235081713 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (56671311527 / 2500000000000 : ℝ))
      (E := (cell12578 ⟨34, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (16580235081713 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (56671311527 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_35 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41433495640783 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266856437139 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨35, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41433495640783 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266856437139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_36 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (10354103875069 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133430227277 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨36, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (10354103875069 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133430227277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_37 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41399347267409 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266864455417 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨37, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41399347267409 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266864455417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_38 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (82764581853813 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133434220097 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨38, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (82764581853813 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133434220097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_39 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (10341311615893 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266872467839 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨39, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (10341311615893 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266872467839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12579_20 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83382265576727 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133334534467 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨20, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83382265576727 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133334534467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_21 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83347744608149 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (283334131691 / 12500000000000 : ℝ))
      (E := (cell12579 ⟨21, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83347744608149 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (283334131691 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_22 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (10414155991487 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141667315367 / 6250000000000 : ℝ))
      (E := (cell12579 ⟨22, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (10414155991487 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141667315367 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_23 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83278775514979 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133340524977 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨23, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83278775514979 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133340524977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_24 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83244327324579 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266685069529 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨24, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83244327324579 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266685069529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_25 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83209903328047 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266689049727 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨25, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83209903328047 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266689049727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_26 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83175503492899 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266693052169 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨26, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83175503492899 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266693052169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_27 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83141127786819 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266697079901 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨27, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83141127786819 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266697079901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_28 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (10388347022207 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133350538643 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨28, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (10388347022207 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133350538643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_29 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41536224316713 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141669065427 / 6250000000000 : ℝ))
      (E := (cell12579 ⟨29, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41536224316713 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141669065427 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_30 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41519072561153 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133354524661 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨30, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41519072561153 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133354524661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_31 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (20750966403159 / 25000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133356543439 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨31, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (20750966403159 / 25000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133356543439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_32 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41484805036459 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133358522147 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨32, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41484805036459 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133358522147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_33 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (16587075694363 / 20000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266721098807 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨33, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (16587075694363 / 20000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266721098807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_34 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (20725292694537 / 25000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266725076139 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨34, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (20725292694537 / 25000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266725076139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_35 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (828669869609 / 1000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (35417642103 / 1562500000000 : ℝ))
      (E := (cell12579 ⟨35, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (828669869609 / 1000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (35417642103 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_36 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82832826989207 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (35417704633 / 1562500000000 : ℝ))
      (E := (cell12579 ⟨36, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82832826989207 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (35417704633 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_37 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41399345416183 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (283342135323 / 12500000000000 : ℝ))
      (E := (cell12579 ⟨37, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41399345416183 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (283342135323 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_38 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82764578459827 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266741053273 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨38, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82764578459827 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266741053273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_39 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (82730489841197 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266745067533 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨39, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (82730489841197 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266745067533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12580_20 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83382256565957 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266541748439 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨20, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83382256565957 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266541748439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_21 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (16669547182637 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133272882547 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨21, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (16669547182637 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133272882547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_22 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83313239552297 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566637432987 / 25000000000000 : ℝ))
      (E := (cell12580 ⟨22, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83313239552297 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566637432987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_23 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41639383725153 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (283319221199 / 12500000000000 : ℝ))
      (E := (cell12580 ⟨23, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41639383725153 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (283319221199 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_24 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (10405539946799 / 12500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266557765131 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨24, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (10405539946799 / 12500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266557765131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_25 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (20802473972977 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133280861003 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨25, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (20802473972977 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133280861003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_26 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (8317549637037 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453313152049 / 20000000000000 : ℝ))
      (E := (cell12580 ⟨26, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (8317549637037 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453313152049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_27 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (10392640122183 / 12500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266569766103 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨27, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (10392640122183 / 12500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266569766103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_28 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83106769681041 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133286871161 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨28, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83106769681041 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133286871161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_29 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41536221224557 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266577749893 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨29, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41536221224557 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266577749893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_30 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (10379767406233 / 12500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266581732663 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨30, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (10379767406233 / 12500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266581732663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_31 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (8300386005163 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (283323218901 / 12500000000000 : ℝ))
      (E := (cell12580 ⟨31, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (8300386005163 / 10000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (283323218901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_32 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (82969604822917 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566647437217 / 25000000000000 : ℝ))
      (E := (cell12580 ⟨32, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (82969604822917 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566647437217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_33 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (82935373532387 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566648431809 / 25000000000000 : ℝ))
      (E := (cell12580 ⟨33, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (82935373532387 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566648431809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_34 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (82901166148863 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (70831179571 / 3125000000000 : ℝ))
      (E := (cell12580 ⟨34, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (82901166148863 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (70831179571 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_35 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (82866982641327 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133300874283 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨35, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (82866982641327 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133300874283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_36 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41416411489459 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566651433757 / 25000000000000 : ℝ))
      (E := (cell12580 ⟨36, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41416411489459 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566651433757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_37 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (20699671782733 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133304882507 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨37, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (20699671782733 / 25000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133304882507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_38 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (82764575066821 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133306890183 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨38, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (82764575066821 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133306890183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_39 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (2585327711131 / 3125000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133308890663 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨39, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (2585327711131 / 3125000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133308890663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12581_20 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (16676449511371 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266414482143 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨20, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (16676449511371 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266414482143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_21 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (1666954544397 / 2000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (283302309079 / 12500000000000 : ℝ))
      (E := (cell12581 ⟨21, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (1666954544397 / 2000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (283302309079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_22 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83313231174289 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266422472349 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨22, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83313231174289 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266422472349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_23 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (5204922461699 / 6250000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133213242641 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨23, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (5204922461699 / 6250000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133213242641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_24 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83244311825719 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133215228411 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨24, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83244311825719 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133215228411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_25 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (20802472114311 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133217224399 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨25, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (20802472114311 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133217224399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_26 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41587744624639 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (226643846449 / 10000000000000 : ℝ))
      (E := (cell12581 ⟨26, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41587744624639 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (226643846449 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_27 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (20785278542377 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (17706581629 / 781250000000 : ℝ))
      (E := (cell12581 ⟨27, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (20785278542377 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (17706581629 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_28 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (16621352637157 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266446462061 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨28, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (16621352637157 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266446462061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_29 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (20768109066531 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266450449241 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨29, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (20768109066531 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266450449241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_30 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (16607626675741 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (141653404427 / 6250000000000 : ℝ))
      (E := (cell12581 ⟨30, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (16607626675741 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (141653404427 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_31 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (8300385449187 / 10000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266458470427 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨31, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (8300385449187 / 10000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266458470427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_32 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82969599574123 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133231224923 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨32, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82969599574123 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133231224923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_33 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (5183460537133 / 6250000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566616617313 / 25000000000000 : ℝ))
      (E := (cell12581 ⟨33, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (5183460537133 / 6250000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566616617313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_34 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (20725290380177 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566617617871 / 25000000000000 : ℝ))
      (E := (cell12581 ⟨34, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (20725290380177 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566617617871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_35 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (82866978322847 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133237228839 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨35, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (82866978322847 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133237228839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_36 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (20708204742421 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266478487389 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨36, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (20708204742421 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266478487389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_37 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (16559736686103 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566620625677 / 25000000000000 : ℝ))
      (E := (cell12581 ⟨37, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (16559736686103 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566620625677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_38 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (16552914334959 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (70827703253 / 3125000000000 : ℝ))
      (E := (cell12581 ⟨38, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (16552914334959 / 20000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (70827703253 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_39 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (8273048367213 / 10000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (453298098359 / 20000000000000 : ℝ))
      (E := (cell12581 ⟨39, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (8273048367213 / 10000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (453298098359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12582_20 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83382238549421 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266287211781 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨20, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83382238549421 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266287211781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_21 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (5209232408009 / 6250000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133145617217 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨21, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (5209232408009 / 6250000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133145617217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_22 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83313222797871 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266295208763 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨22, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83313222797871 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266295208763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_23 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (41639375662807 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133149627681 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨23, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (41639375662807 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133149627681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_24 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (41622152039279 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (141643953833 / 6250000000000 : ℝ))
      (E := (cell12582 ⟨24, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (41622152039279 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (141643953833 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_25 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (41604940512027 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133153615053 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨25, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (41604940512027 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133153615053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_26 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (41587741064811 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133155611657 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨26, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (41587741064811 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133155611657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_27 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (1662822147259 / 2000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133157621997 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨27, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (1662822147259 / 2000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133157621997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_28 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (5194172293243 / 6250000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453263847301 / 20000000000000 : ℝ))
      (E := (cell12582 ⟨28, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (5194172293243 / 6250000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453263847301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_29 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (41536215042227 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (566580815459 / 25000000000000 : ℝ))
      (E := (cell12582 ⟨29, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (41536215042227 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (566580815459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_30 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83038127508829 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (226632726383 / 10000000000000 : ℝ))
      (E := (cell12582 ⟨30, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83038127508829 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (226632726383 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_31 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (16600769786671 / 20000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133165622269 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨31, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (16600769786671 / 20000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133165622269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_32 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (10371199290817 / 12500000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266335264327 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨32, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (10371199290817 / 12500000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266335264327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_33 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (82935363657037 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133169633143 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨33, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (82935363657037 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133169633143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_34 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (20725289223421 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (35411613309 / 1562500000000 : ℝ))
      (E := (cell12582 ⟨34, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (20725289223421 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (35411613309 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_35 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (4143348700273 / 5000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266347221933 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨35, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (4143348700273 / 5000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266347221933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_36 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (2588525467547 / 3125000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (283293904539 / 12500000000000 : ℝ))
      (E := (cell12582 ⟨36, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (2588525467547 / 3125000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (283293904539 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_37 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (20699669932779 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133177618501 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨37, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (20699669932779 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133177618501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_38 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (20691142070937 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133179612233 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨38, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (20691142070937 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133179612233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_39 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (82730480589009 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453272651531 / 20000000000000 : ℝ))
      (E := (cell12582 ⟨39, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (82730480589009 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453272651531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12583_20 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (83382229543653 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266160053887 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨20, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (83382229543653 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266160053887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_21 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (83347709838067 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133082025249 / 50000000000000 : ℝ))
      (E := (cell12583 ⟨21, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (83347709838067 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133082025249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_22 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (83313214423043 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266168057817 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨22, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (83313214423043 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266168057817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_23 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20819685816399 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266172021493 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨23, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20819685816399 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266172021493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_24 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (8324429633291 / 10000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (90647042477 / 4000000000000 : ℝ))
      (E := (cell12583 ⟨24, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (8324429633291 / 10000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (90647042477 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_25 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41604936796169 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266180065931 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨25, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41604936796169 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266180065931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_26 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41587737505701 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566546009179 / 25000000000000 : ℝ))
      (E := (cell12583 ⟨26, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41587737505701 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566546009179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_27 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20785275139447 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266188035687 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨27, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20785275139447 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266188035687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_28 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (83106750199351 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266192065653 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨28, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (83106750199351 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266192065653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_29 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41536211952053 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133098035359 / 50000000000000 : ℝ))
      (E := (cell12583 ⟨29, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41536211952053 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133098035359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_30 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20759530410059 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266200053157 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨30, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20759530410059 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266200053157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_31 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20750960844021 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133102007509 / 50000000000000 : ℝ))
      (E := (cell12583 ⟨31, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20750960844021 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133102007509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_32 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (16593917816031 / 20000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266208016667 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨32, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (16593917816031 / 20000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266208016667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_33 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20733839680279 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566553014941 / 25000000000000 : ℝ))
      (E := (cell12583 ⟨33, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20733839680279 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566553014941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_34 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (82901152267791 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266216028551 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨34, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (82901152267791 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266216028551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_35 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (16573393937833 / 20000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (226622004133 / 10000000000000 : ℝ))
      (E := (cell12583 ⟨35, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (16573393937833 / 20000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (226622004133 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_36 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (4141640547719 / 5000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266224040439 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨36, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (4141640547719 / 5000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266224040439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_37 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41399338016367 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266228026563 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨37, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41399338016367 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266228026563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_38 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (82764564893681 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266232058853 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨38, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (82764564893681 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266232058853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_39 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (8273047750683 / 10000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (453247215781 / 20000000000000 : ℝ))
      (E := (cell12583 ⟨39, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (8273047750683 / 10000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (453247215781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12584_20 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83382220539553 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266032891927 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨20, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83382220539553 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266032891927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_21 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83347701149617 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266036862539 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨21, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83347701149617 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266036862539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_22 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (20828301512451 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266040902887 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨22, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (20828301512451 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266040902887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_23 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (10409841900891 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266044900353 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨23, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (10409841900891 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266044900353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_24 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41622144294387 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133024458489 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨24, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41622144294387 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133024458489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_25 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83209866162097 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266052897887 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨25, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83209866162097 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266052897887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_26 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83175467894617 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133028452349 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨26, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83175467894617 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133028452349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_27 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (10392636719253 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133030441011 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨27, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (10392636719253 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133030441011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_28 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (20776685927043 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566516222763 / 25000000000000 : ℝ))
      (E := (cell12584 ⟨28, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (20776685927043 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566516222763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_29 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41536208862539 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (226606887589 / 10000000000000 : ℝ))
      (E := (cell12584 ⟨29, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41536208862539 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (226606887589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_30 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (20759528943231 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453214579463 / 20000000000000 : ℝ))
      (E := (cell12584 ⟨30, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (20759528943231 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453214579463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_31 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83003837820057 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453215379783 / 20000000000000 : ℝ))
      (E := (cell12584 ⟨31, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83003837820057 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453215379783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_32 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (4148479191749 / 5000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266080882511 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨32, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (4148479191749 / 5000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266080882511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_33 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41467676893181 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266084908261 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨33, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41467676893181 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266084908261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_34 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (20725286910757 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133044459501 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨34, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (20725286910757 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133044459501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_35 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (82866965373963 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266092915869 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨35, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (82866965373963 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266092915869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_36 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (8283280694831 / 10000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266096899771 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨36, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (8283280694831 / 10000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266096899771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_37 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (10349834041921 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266100871391 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨37, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (10349834041921 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266100871391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_38 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (5172785094037 / 6250000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266104889881 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨38, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (5172785094037 / 6250000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266104889881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_39 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (10341309303199 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453221779367 / 20000000000000 : ℝ))
      (E := (cell12584 ⟨39, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (10341309303199 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453221779367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12585_20 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41691105768559 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566476446043 / 25000000000000 : ℝ))
      (E := (cell12585 ⟨20, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41691105768559 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566476446043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_21 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (16669538492559 / 20000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265909787137 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨21, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (16669538492559 / 20000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265909787137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_22 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41656598839077 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265913802287 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨22, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41656598839077 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265913802287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_23 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (8327872715021 / 10000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226591777527 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨23, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (8327872715021 / 10000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226591777527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_24 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (1664885616923 / 2000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (3625474829 / 160000000000 : ℝ))
      (E := (cell12585 ⟨24, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (1664885616923 / 2000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (3625474829 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_25 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (5200616170833 / 6250000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566481446091 / 25000000000000 : ℝ))
      (E := (cell12585 ⟨25, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (5200616170833 / 6250000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566481446091 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_26 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (83175460779267 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (453185953771 / 20000000000000 : ℝ))
      (E := (cell12585 ⟨26, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (83175460779267 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (453185953771 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_27 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (83141086951657 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265933783001 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨27, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (83141086951657 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265933783001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_28 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (83106737218351 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265937771159 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨28, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (83106737218351 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265937771159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_29 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (8307241154737 / 10000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265941794311 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨29, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (8307241154737 / 10000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265941794311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_30 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (16607621981379 / 20000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (453189159261 / 20000000000000 : ℝ))
      (E := (cell12585 ⟨30, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (16607621981379 / 20000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (453189159261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_31 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (83003832265273 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (141621861199 / 6250000000000 : ℝ))
      (E := (cell12585 ⟨31, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (83003832265273 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (141621861199 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_32 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (82969578591011 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265953803313 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨32, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (82969578591011 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265953803313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_33 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (10366918606597 / 12500000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132978905889 / 50000000000000 : ℝ))
      (E := (cell12585 ⟨33, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (10366918606597 / 12500000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132978905889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_34 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41450571509697 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265961805941 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨34, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41450571509697 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265961805941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_35 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (20716740264963 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (453193157387 / 20000000000000 : ℝ))
      (E := (cell12585 ⟨35, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (20716740264963 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (453193157387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_36 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41416401471647 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226596981431 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨36, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41416401471647 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226596981431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_37 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41399334319509 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226597377149 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨37, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41399334319509 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226597377149 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_38 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41382279058241 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (28324722203 / 1250000000000 : ℝ))
      (E := (cell12585 ⟨38, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41382279058241 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (28324722203 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_39 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41365235672647 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265981770159 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨39, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41365235672647 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265981770159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12586_20 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (83382202536349 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265778730623 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨20, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (83382202536349 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265778730623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_21 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (83347683777601 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (4425356851 / 195312500000 : ℝ))
      (E := (cell12586 ⟨21, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (83347683777601 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (4425356851 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_22 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (83313189308093 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (283223337213 / 12500000000000 : ℝ))
      (E := (cell12586 ⟨22, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (83313189308093 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (283223337213 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_23 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41639359547421 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132895352291 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨23, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41639359547421 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132895352291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_24 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (83244273105037 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566448683023 / 25000000000000 : ℝ))
      (E := (cell12586 ⟨24, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (83244273105037 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566448683023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_25 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (5200615706627 / 6250000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265798725361 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨25, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (5200615706627 / 6250000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265798725361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_26 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (10396931708169 / 12500000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (453160537519 / 20000000000000 : ℝ))
      (E := (cell12586 ⟨26, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (10396931708169 / 12500000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (453160537519 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_27 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (16628216030137 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566451684657 / 25000000000000 : ℝ))
      (E := (cell12586 ⟨27, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (16628216030137 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566451684657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_28 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (2597085335309 / 3125000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (90632428239 / 4000000000000 : ℝ))
      (E := (cell12586 ⟨28, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (2597085335309 / 3125000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (90632428239 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_29 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (83072405370981 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132907354513 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨29, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (83072405370981 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132907354513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_30 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (20759526010537 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265818691627 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨30, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (20759526010537 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265818691627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_31 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41501913355867 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566455678587 / 25000000000000 : ℝ))
      (E := (cell12586 ⟨31, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41501913355867 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566455678587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_32 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82969573348247 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (90633068821 / 4000000000000 : ℝ))
      (E := (cell12586 ⟨32, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82969573348247 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (90633068821 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_33 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82935343920357 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (453166142349 / 20000000000000 : ℝ))
      (E := (cell12586 ⟨33, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82935343920357 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (453166142349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_34 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (8290113839689 / 10000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566458686991 / 25000000000000 : ℝ))
      (E := (cell12586 ⟨34, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (8290113839689 / 10000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566458686991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_35 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41433478373417 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132919356573 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨35, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41433478373417 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132919356573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_36 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (82832798939331 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (283230340677 / 12500000000000 : ℝ))
      (E := (cell12586 ⟨36, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (82832798939331 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (283230340677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_37 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (16559732988737 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132923363429 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨37, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (16559732988737 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132923363429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_38 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (1655291094587 / 2000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265850717933 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨38, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (1655291094587 / 2000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265850717933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_39 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41365234132969 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566463674719 / 25000000000000 : ℝ))
      (E := (cell12586 ⟨39, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41365234132969 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566463674719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12587_20 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41691096768623 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265651673011 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨20, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41691096768623 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265651673011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_21 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (5209229693377 / 6250000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265655682557 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨21, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (5209229693377 / 6250000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265655682557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_22 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83313180939619 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265659705767 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨22, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83313180939619 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265659705767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_23 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (81326866251 / 97656250000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265663688287 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨23, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (81326866251 / 97656250000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265663688287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_24 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (16648853073087 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (453133538431 / 20000000000000 : ℝ))
      (E := (cell12587 ⟨24, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (16648853073087 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (453133538431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_25 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83209843880209 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132835831247 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨25, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83209843880209 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132835831247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_26 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83175446552871 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132837830459 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨26, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83175446552871 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132837830459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_27 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (8314107335111 / 10000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265679690469 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨27, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (8314107335111 / 10000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265679690469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_28 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83106724242783 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265683695499 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨28, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83106724242783 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265683695499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_29 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (10384049899489 / 12500000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (141605479907 / 6250000000000 : ℝ))
      (E := (cell12587 ⟨29, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (10384049899489 / 12500000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (141605479907 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_30 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83038098178681 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132845850143 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨30, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83038098178681 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132845850143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_31 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83003821159437 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265695704409 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨31, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83003821159437 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265695704409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_32 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82969568106689 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (283212461587 / 12500000000000 : ℝ))
      (E := (cell12587 ⟨32, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82969568106689 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (283212461587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_33 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (16587067797821 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265703666733 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨33, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (16587067797821 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265703666733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_34 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (16580226755103 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (90628307459 / 4000000000000 : ℝ))
      (E := (cell12587 ⟨34, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (16580226755103 / 20000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (90628307459 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_35 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41433476217453 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (283213961813 / 12500000000000 : ℝ))
      (E := (cell12587 ⟨35, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41433476217453 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (283213961813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_36 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82832794936423 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265715691729 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨36, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82832794936423 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265715691729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_37 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (82798661249367 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265719678831 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨37, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (82798661249367 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265719678831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_38 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (20691137835799 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265723714957 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨38, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (20691137835799 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265723714957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_39 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41365232593761 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265727682989 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨39, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41365232593761 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265727682989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12588_20 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (83382184539807 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132762363937 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨20, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (83382184539807 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132762363937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_21 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (8334766641209 / 10000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (283191088959 / 12500000000000 : ℝ))
      (E := (cell12588 ⟨21, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (8334766641209 / 10000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (283191088959 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_22 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (83313172572733 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265532709849 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨22, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (83313172572733 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265532709849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_23 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (16655740597751 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265536726389 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨23, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (16655740597751 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265536726389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_24 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (5202766101709 / 6250000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566385176669 / 25000000000000 : ℝ))
      (E := (cell12588 ⟨24, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (5202766101709 / 6250000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566385176669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_25 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (83209836455859 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265544712533 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨25, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (83209836455859 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265544712533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_26 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (83175439441823 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132774344413 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨26, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (83175439441823 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132774344413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_27 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (8314106655293 / 10000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265552696957 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨27, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (8314106655293 / 10000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265552696957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_28 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (20776679439259 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265556681277 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨28, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (20776679439259 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265556681277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_29 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (41536196511081 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265560702771 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨29, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (41536196511081 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265560702771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_30 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (5189880769781 / 6250000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265564705277 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨30, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (5189880769781 / 6250000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265564705277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_31 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (83003815608383 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265568690843 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨31, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (83003815608383 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265568690843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_32 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (16593912573267 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265572719827 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨32, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (16593912573267 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265572719827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_33 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (4146766702951 / 5000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566394183829 / 25000000000000 : ℝ))
      (E := (cell12588 ⟨33, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (4146766702951 / 5000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566394183829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_34 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82901129155269 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226558068007 / 10000000000000 : ℝ))
      (E := (cell12588 ⟨34, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82901129155269 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226558068007 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_35 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82866948124069 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226558473101 / 10000000000000 : ℝ))
      (E := (cell12588 ⟨35, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82866948124069 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226558473101 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_36 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82832790934567 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566397178313 / 25000000000000 : ℝ))
      (E := (cell12588 ⟨36, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82832790934567 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566397178313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_37 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (2587458048627 / 3125000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566398171519 / 25000000000000 : ℝ))
      (E := (cell12588 ⟨37, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (2587458048627 / 3125000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (566398171519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_38 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (82764547958019 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265596708627 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨38, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (82764547958019 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265596708627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_39 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (16546092422009 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132800361249 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨39, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (16546092422009 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132800361249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12589_20 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83382175544033 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265397778679 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨20, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83382175544033 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265397778679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_21 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41673828865887 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (35396902137 / 1562500000000 : ℝ))
      (E := (cell12589 ⟨21, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41673828865887 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (35396902137 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_22 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (16662632841487 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132702884133 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨22, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (16662632841487 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132702884133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_23 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (16655738987607 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265409760551 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨23, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (16655738987607 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265409760551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_24 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83244249890763 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265413775659 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨24, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83244249890763 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265413775659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_25 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (4160491451649 / 5000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265417758711 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨25, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (4160491451649 / 5000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265417758711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_26 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83175432332209 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265421771321 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨26, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83175432332209 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265421771321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_27 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (16628211951229 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132712879047 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨27, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (16628211951229 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132712879047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_28 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (16621342254529 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265429780223 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨28, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (16621342254529 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265429780223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_29 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83072386849731 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265433781803 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨29, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83072386849731 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265433781803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_30 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83038086455591 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132718882553 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨30, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83038086455591 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132718882553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_31 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (20750952514643 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265441790701 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨31, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (20750952514643 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265441790701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_32 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41484778813593 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265445743371 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨32, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41484778813593 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265445743371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_33 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41467664565051 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132724870889 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨33, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41467664565051 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132724870889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_34 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (10362640567019 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566363446837 / 25000000000000 : ℝ))
      (E := (cell12589 ⟨34, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (10362640567019 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566363446837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_35 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82866943814323 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (453091552809 / 20000000000000 : ℝ))
      (E := (cell12589 ⟨35, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82866943814323 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (453091552809 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_36 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (20708196733441 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265461789987 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨36, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (20708196733441 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265461789987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_37 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82798653863777 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132732874297 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨37, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82798653863777 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132732874297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_38 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (4138227228691 / 5000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (35397964963 / 1562500000000 : ℝ))
      (E := (cell12589 ⟨38, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (4138227228691 / 5000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (35397964963 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_39 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (82730459033509 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265473758691 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨39, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (82730459033509 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265473758691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12590_20 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83382166549923 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132635441847 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨20, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83382166549923 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132635441847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_21 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20836912263271 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265274874427 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨21, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20836912263271 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265274874427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_22 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83313155843723 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (113263944051 / 5000000000000 : ℝ))
      (E := (cell12590 ⟨22, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83313155843723 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (113263944051 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_23 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41639343444431 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265282849113 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨23, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41639343444431 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265282849113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_24 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20811060538923 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265286840743 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨24, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20811060538923 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265286840743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_25 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20802455402893 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453058171883 / 20000000000000 : ℝ))
      (E := (cell12590 ⟨25, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20802455402893 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453058171883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_26 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20793856306007 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453058969999 / 20000000000000 : ℝ))
      (E := (cell12590 ⟨26, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20793856306007 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453058969999 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_27 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (16628210592151 / 20000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132649436941 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨27, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (16628210592151 / 20000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132649436941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_28 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (8310670478961 / 10000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566325718857 / 25000000000000 : ℝ))
      (E := (cell12590 ⟨28, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (8310670478961 / 10000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566325718857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_29 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41536190339309 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132653428567 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨29, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41536190339309 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132653428567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_30 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41519040297983 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132655439887 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨30, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41519040297983 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132655439887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_31 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83003804510003 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453062977387 / 20000000000000 : ℝ))
      (E := (cell12590 ⟨31, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83003804510003 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453062977387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_32 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (2074238809731 / 2500000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265318880429 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨32, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (2074238809731 / 2500000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265318880429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_33 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (1658706484047 / 2000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265322861839 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨33, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (1658706484047 / 2000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265322861839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_34 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41450559959081 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (28316586139 / 1250000000000 : ℝ))
      (E := (cell12590 ⟨34, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41450559959081 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (28316586139 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_35 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20716734876417 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (226533085223 / 10000000000000 : ℝ))
      (E := (cell12590 ⟨35, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20716734876417 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (226533085223 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_36 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41416391467007 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265334863291 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨36, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41416391467007 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265334863291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_37 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (10349831271563 / 12500000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566334716597 / 25000000000000 : ℝ))
      (E := (cell12590 ⟨37, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (10349831271563 / 12500000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566334716597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_38 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (82764541190599 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265342861973 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨38, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (82764541190599 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265342861973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_39 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (10341306994739 / 12500000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265346850283 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨39, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (10341306994739 / 12500000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265346850283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12591_20 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (83382157557477 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265143984651 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨20, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (83382157557477 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265143984651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_21 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41673820188009 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (226514800807 / 10000000000000 : ℝ))
      (E := (cell12591 ⟨21, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41673820188009 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (226514800807 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_22 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41656573740799 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (453030397959 / 20000000000000 : ℝ))
      (E := (cell12591 ⟨22, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41656573740799 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (453030397959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_23 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41639339420619 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (90606239683 / 4000000000000 : ℝ))
      (E := (cell12591 ⟨23, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41639339420619 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (90606239683 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_24 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (83244234422131 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (45303200373 / 2000000000000 : ℝ))
      (E := (cell12591 ⟨24, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (83244234422131 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (45303200373 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_25 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20802453547909 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566291003661 / 25000000000000 : ℝ))
      (E := (cell12591 ⟨25, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20802453547909 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566291003661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_26 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (519846363233 / 625000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132583991629 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨26, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (519846363233 / 625000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132583991629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_27 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (83141046166759 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (226517198589 / 10000000000000 : ℝ))
      (E := (cell12591 ⟨27, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (83141046166759 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (226517198589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_28 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20776674576983 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132588012673 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨28, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20776674576983 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132588012673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_29 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (83072374508823 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265179987241 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨29, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (83072374508823 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265179987241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_30 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (83038074737621 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265183990779 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨30, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (83038074737621 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265183990779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_31 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (3320151958507 / 4000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132593989773 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨31, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (3320151958507 / 4000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132593989773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_32 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82969547152499 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265192013901 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨32, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82969547152499 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265192013901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_33 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82935319275763 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (453039195671 / 20000000000000 : ℝ))
      (E := (cell12591 ⟨33, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82935319275763 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (453039195671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_34 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (82901115301301 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265199991383 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨34, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (82901115301301 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265199991383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_35 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41433467599051 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265203995567 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨35, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41433467599051 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265203995567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_36 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20708194733829 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265207991809 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨36, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20708194733829 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265207991809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_37 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41399323241123 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (70787876233 / 3125000000000 : ℝ))
      (E := (cell12591 ⟨37, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41399323241123 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (70787876233 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_38 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41382268904177 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265216021653 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨38, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41382268904177 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265216021653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_39 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41365226441627 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566304999319 / 25000000000000 : ℝ))
      (E := (cell12591 ⟨39, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41365226441627 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566304999319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12592_20 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41691074283347 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265017198089 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨20, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41691074283347 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265017198089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_21 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (83347631700577 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (566255298997 / 25000000000000 : ℝ))
      (E := (cell12592 ⟨21, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (83347631700577 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (566255298997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_22 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (83313139121059 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265025152909 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨22, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (83313139121059 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265025152909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_23 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41639335397581 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (566257297359 / 25000000000000 : ℝ))
      (E := (cell12592 ⟨23, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41639335397581 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (566257297359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_24 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41622113345039 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265033192661 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨24, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41622113345039 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265033192661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_25 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (8320980677317 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453007433203 / 20000000000000 : ℝ))
      (E := (cell12592 ⟨25, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (8320980677317 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453007433203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_26 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (20793852752991 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (226504117111 / 10000000000000 : ℝ))
      (E := (cell12592 ⟨26, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (20793852752991 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (226504117111 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_27 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (83141039374157 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (45300903051 / 2000000000000 : ℝ))
      (E := (cell12592 ⟨27, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (83141039374157 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (45300903051 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_28 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (83106691827609 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (90601966861 / 4000000000000 : ℝ))
      (E := (cell12592 ⟨28, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (83106691827609 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (90601966861 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_29 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41536184170173 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (18120425377 / 800000000000 : ℝ))
      (E := (cell12592 ⟨29, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41536184170173 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (18120425377 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_30 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (16607613776111 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (141566072289 / 6250000000000 : ℝ))
      (E := (cell12592 ⟨30, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (16607613776111 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (141566072289 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_31 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (83003793416589 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (141566324099 / 6250000000000 : ℝ))
      (E := (cell12592 ⟨31, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (83003793416589 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (141566324099 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_32 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (518559636981 / 625000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265065202339 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨32, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (518559636981 / 625000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265065202339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_33 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41467657175171 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (226506920847 / 10000000000000 : ℝ))
      (E := (cell12592 ⟨33, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41467657175171 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (226506920847 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_34 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (82901110685567 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (566268301333 / 25000000000000 : ℝ))
      (E := (cell12592 ⟨34, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (82901110685567 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (566268301333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_35 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41433465445813 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (283134649257 / 12500000000000 : ℝ))
      (E := (cell12592 ⟨35, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41433465445813 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (283134649257 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_36 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (8283277493767 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265081175541 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨36, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (8283277493767 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265081175541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_37 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41399321396501 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453017041827 / 20000000000000 : ℝ))
      (E := (cell12592 ⟨37, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41399321396501 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453017041827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_38 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (16552906885417 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265089177981 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨38, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (16552906885417 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265089177981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_39 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (646331639137 / 781250000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265093199667 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨39, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (646331639137 / 781250000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265093199667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12593_20 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41691069788787 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (141555650467 / 6250000000000 : ℝ))
      (E := (cell12593 ⟨20, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41691069788787 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (141555650467 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_21 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (2083690575669 / 2500000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264894379891 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨21, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (2083690575669 / 2500000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264894379891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_22 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (16662626152421 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264898428677 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨22, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (16662626152421 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264898428677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_23 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (10409832843829 / 12500000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (141556398929 / 6250000000000 : ℝ))
      (E := (cell12593 ⟨23, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (10409832843829 / 12500000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (141556398929 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_24 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41622109479767 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (141556651321 / 6250000000000 : ℝ))
      (E := (cell12593 ⟨24, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41622109479767 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (141556651321 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_25 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41604899678087 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264910430299 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨25, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41604899678087 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264910430299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_26 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (1039692548851 / 1250000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264914413553 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨26, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (1039692548851 / 1250000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264914413553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_27 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83141032582949 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (283114804037 / 12500000000000 : ℝ))
      (E := (cell12593 ⟨27, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83141032582949 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (283114804037 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_28 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41553342674321 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132461215437 / 50000000000000 : ℝ))
      (E := (cell12593 ⟨28, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41553342674321 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132461215437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_29 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41536181086593 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566231602947 / 25000000000000 : ℝ))
      (E := (cell12593 ⟨29, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41536181086593 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566231602947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_30 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83038063024769 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264930435811 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨30, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83038063024769 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264930435811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_31 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (162116773187 / 195312500000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566233597 / 25000000000 : ℝ))
      (E := (cell12593 ⟨31, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (162116773187 / 195312500000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566233597 / 25000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_32 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (663756293461 / 800000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264938387193 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨32, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (663756293461 / 800000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264938387193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_33 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41467654713043 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264942435041 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨33, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41467654713043 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264942435041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_34 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (1036263825887 / 1250000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264946415777 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨34, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (1036263825887 / 1250000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264946415777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_35 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (129479572791 / 156250000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264950389077 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨35, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (129479572791 / 156250000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264950389077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_36 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (3313310837643 / 4000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264954414489 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨36, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (3313310837643 / 4000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264954414489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_37 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20699659776193 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264958434091 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨37, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20699659776193 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264958434091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_38 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (82764531046793 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264962389649 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨38, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (82764531046793 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264962389649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_39 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20682611684189 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566241599687 / 25000000000000 : ℝ))
      (E := (cell12593 ⟨39, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20682611684189 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566241599687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12594_20 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20845532647529 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (226476367107 / 10000000000000 : ℝ))
      (E := (cell12594 ⟨20, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20845532647529 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (226476367107 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_21 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83347614354567 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566191919091 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨21, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83347614354567 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566191919091 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_22 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83313122404737 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566192910539 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨22, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83313122404737 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566192910539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_23 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83278654707649 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264775689033 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨23, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83278654707649 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264775689033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_24 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83244211230499 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566194911429 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨24, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83244211230499 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566194911429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_25 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (10401223992581 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (283097961341 / 12500000000000 : ℝ))
      (E := (cell12594 ⟨25, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (10401223992581 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (283097961341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_26 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20793849201407 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (113239382609 / 5000000000000 : ℝ))
      (E := (cell12594 ⟨26, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20793849201407 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (113239382609 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_27 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (41570512896567 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (283098956229 / 12500000000000 : ℝ))
      (E := (cell12594 ⟨27, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (41570512896567 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (283098956229 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_28 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (8310667887103 / 10000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132397843243 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨28, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (8310667887103 / 10000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132397843243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_29 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (41536178003671 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132399823877 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨29, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (41536178003671 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132399823877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_30 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83038057170261 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132401826419 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨30, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83038057170261 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132401826419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_31 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (4150189116407 / 5000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132403822661 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨31, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (4150189116407 / 5000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132403822661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_32 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82969531449493 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566202921391 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨32, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82969531449493 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566202921391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_33 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (16587060900599 / 20000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264815658069 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨33, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (16587060900599 / 20000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264815658069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_34 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82901101457481 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264819681313 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨34, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82901101457481 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264819681313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_35 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82866922281943 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132411848937 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨35, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82866922281943 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132411848937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_36 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20708191736383 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (226482765001 / 10000000000000 : ℝ))
      (E := (cell12594 ⟨36, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20708191736383 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (226482765001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_37 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20699658854389 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264831655659 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨37, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20699658854389 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264831655659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_38 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (82764527667477 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264835656657 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨38, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (82764527667477 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264835656657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_39 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (41365221832457 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (452967942389 / 20000000000000 : ℝ))
      (E := (cell12594 ⟨39, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (41365221832457 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (452967942389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12595_20 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (521138260027 / 625000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452927397777 / 20000000000000 : ℝ))
      (E := (cell12595 ⟨20, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (521138260027 / 625000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452927397777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_21 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83347605683997 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (283080121103 / 12500000000000 : ℝ))
      (E := (cell12595 ⟨21, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83347605683997 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (283080121103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_22 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83313114048953 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264644968293 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨22, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83313114048953 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264644968293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_23 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83278646666213 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566162247817 / 25000000000000 : ℝ))
      (E := (cell12595 ⟨23, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83278646666213 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566162247817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_24 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83244203502971 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264652983127 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨24, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83244203502971 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264652983127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_25 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (325038220807 / 390625000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132328473651 / 50000000000000 : ℝ))
      (E := (cell12595 ⟨25, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (325038220807 / 390625000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132328473651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_26 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41587694852303 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264660945401 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨26, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41587694852303 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264660945401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_27 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (10392627375589 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264664980457 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨27, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (10392627375589 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264664980457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_28 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83106672394773 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (141541812301 / 6250000000000 : ℝ))
      (E := (cell12595 ⟨28, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83106672394773 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (141541812301 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_29 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (649002733147 / 781250000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132336498489 / 50000000000000 : ℝ))
      (E := (cell12595 ⟨29, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (649002733147 / 781250000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132336498489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_30 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (10379756414629 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (226467698321 / 10000000000000 : ℝ))
      (E := (cell12595 ⟨30, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (10379756414629 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (226467698321 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_31 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (5187736049111 / 6250000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (45293619151 / 2000000000000 : ℝ))
      (E := (cell12595 ⟨31, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (5187736049111 / 6250000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (45293619151 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_32 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (82969526217563 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132342490177 / 50000000000000 : ℝ))
      (E := (cell12595 ⟨32, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (82969526217563 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132342490177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_33 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (20733824895267 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264688994701 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨33, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (20733824895267 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264688994701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_34 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (10362637105641 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264693001943 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨34, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (10362637105641 / 12500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264693001943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_35 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41433458989367 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264697003207 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨35, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41433458989367 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264697003207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_36 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (129426192111 / 156250000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (70771906231 / 3125000000000 : ℝ))
      (E := (cell12595 ⟨36, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (129426192111 / 156250000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (70771906231 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_37 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (82798631731353 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132352495587 / 50000000000000 : ℝ))
      (E := (cell12595 ⟨37, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (82798631731353 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132352495587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_38 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (82764524289137 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264708979007 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨38, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (82764524289137 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264708979007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_39 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (8273044059401 / 10000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264712963119 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨39, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (8273044059401 / 10000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264712963119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12596_20 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41691056310093 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264510302647 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨20, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41691056310093 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264510302647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_21 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (1666951940301 / 2000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566128578891 / 25000000000000 : ℝ))
      (E := (cell12596 ⟨21, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (1666951940301 / 2000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566128578891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_22 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41656552847377 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264518290457 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨22, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41656552847377 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264518290457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_23 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41639319313161 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264522347909 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨23, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41639319313161 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264522347909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_24 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (83244195776951 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264526316643 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨24, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (83244195776951 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264526316643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_25 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (16641955422801 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (283066289599 / 12500000000000 : ℝ))
      (E := (cell12596 ⟨25, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (16641955422801 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (283066289599 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_26 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (10396922825627 / 12500000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132267146607 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨26, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (10396922825627 / 12500000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132267146607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_27 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (83141012217683 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452907661461 / 20000000000000 : ℝ))
      (E := (cell12596 ⟨27, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (83141012217683 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452907661461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_28 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (8310666591987 / 10000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (226454230341 / 10000000000000 : ℝ))
      (E := (cell12596 ⟨28, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (8310666591987 / 10000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (226454230341 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_29 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (16614468735921 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132273171253 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨29, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (16614468735921 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132273171253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_30 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (83038045465081 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (90582012397 / 4000000000000 : ℝ))
      (E := (cell12596 ⟨30, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (83038045465081 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (90582012397 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_31 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (20750942811163 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452910864937 / 20000000000000 : ℝ))
      (E := (cell12596 ⟨31, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (20750942811163 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452910864937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_32 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (16593904197367 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132279165057 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨32, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (16593904197367 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132279165057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_33 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41467647330153 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264562327791 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨33, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41467647330153 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264562327791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_34 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82901092233901 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (226456631907 / 10000000000000 : ℝ))
      (E := (cell12596 ⟨34, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82901092233901 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (226456631907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_35 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41433456838307 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (90582812203 / 4000000000000 : ℝ))
      (E := (cell12596 ⟨35, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41433456838307 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (90582812203 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_36 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82832758957599 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566143586337 / 25000000000000 : ℝ))
      (E := (cell12596 ⟨36, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82832758957599 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566143586337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_37 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (82798628046163 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264578323303 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨37, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (82798628046163 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264578323303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_38 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (20691130227943 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (22645823567 / 1000000000000 : ℝ))
      (E := (cell12596 ⟨38, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (20691130227943 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (22645823567 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_39 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (16546087504809 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (226458632841 / 10000000000000 : ℝ))
      (E := (cell12596 ⟨39, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (16546087504809 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (226458632841 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12597_20 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (83382103637713 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (8845248941 / 390625000000 : ℝ))
      (E := (cell12597 ⟨20, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (83382103637713 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (8845248941 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_21 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41673794173863 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132193858293 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨21, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41673794173863 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132193858293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_22 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41656548671069 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264391725281 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨22, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41656548671069 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264391725281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_23 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (83278630587977 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264395700619 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨23, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (83278630587977 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264395700619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_24 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (83244188052437 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264399704631 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨24, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (83244188052437 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264399704631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_25 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41604884851443 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264403682431 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨25, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41604884851443 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264403682431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_26 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (10396921938357 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (3623052313 / 160000000000 : ℝ))
      (E := (cell12597 ⟨26, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (10396921938357 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (3623052313 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_27 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (16628201086409 / 20000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132205844407 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨27, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (16628201086409 / 20000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132205844407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_28 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (1038833243079 / 1250000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132207861591 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨28, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (1038833243079 / 1250000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132207861591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_29 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (8307233751771 / 10000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264419684339 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨29, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (8307233751771 / 10000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264419684339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_30 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (10379754951801 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452884738297 / 20000000000000 : ℝ))
      (E := (cell12597 ⟨30, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (10379754951801 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452884738297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_31 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (1296933839137 / 1562500000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132213844101 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨31, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (1296933839137 / 1562500000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132213844101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_32 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82969515757309 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452886346969 / 20000000000000 : ℝ))
      (E := (cell12597 ⟨32, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82969515757309 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452886346969 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_33 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82935289740707 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (566108928979 / 25000000000000 : ℝ))
      (E := (cell12597 ⟨33, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82935289740707 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (566108928979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_34 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (414505438119 / 500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264439691293 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨34, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (414505438119 / 500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264439691293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_35 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (82866909375583 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264443720721 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨35, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (82866909375583 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264443720721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_36 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (10354094370651 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132223873263 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨36, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (10354094370651 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132223873263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_37 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41399312180993 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132225855357 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨37, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41399312180993 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132225855357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_38 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41382258767691 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264455731047 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨38, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41382258767691 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264455731047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_39 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (10341304306877 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (226445974911 / 10000000000000 : ℝ))
      (E := (cell12597 ⟨39, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (10341304306877 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (226445974911 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12598_20 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (833820946569 / 1000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132128575549 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨20, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (833820946569 / 1000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132128575549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_21 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (10418447460253 / 12500000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132130556799 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨21, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (10418447460253 / 12500000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132130556799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_22 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83313088991107 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452853031227 / 20000000000000 : ℝ))
      (E := (cell12598 ⟨22, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83313088991107 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452853031227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_23 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83278622551177 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132134553869 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨23, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83278622551177 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132134553869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_24 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83244180329431 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (226427314709 / 10000000000000 : ℝ))
      (E := (cell12598 ⟨24, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83244180329431 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (226427314709 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_25 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (20802440573309 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264277160989 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨25, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (20802440573309 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264277160989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_26 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (665402947281 / 800000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264281152633 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨26, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (665402947281 / 800000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264281152633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_27 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (415704993239 / 500000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264285124981 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨27, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (415704993239 / 500000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264285124981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_28 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (664853223793 / 800000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (113214456961 / 5000000000000 : ℝ))
      (E := (cell12598 ⟨28, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (664853223793 / 800000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (113214456961 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_29 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83072331357131 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452858627887 / 20000000000000 : ℝ))
      (E := (cell12598 ⟨29, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83072331357131 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452858627887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_30 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (20759508441253 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264297127893 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨30, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (20759508441253 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264297127893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_31 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (20750940041531 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452860233031 / 20000000000000 : ℝ))
      (E := (cell12598 ⟨31, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (20750940041531 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452860233031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_32 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (16593902105797 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132152567999 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨32, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (16593902105797 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132152567999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_33 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (323965956337 / 390625000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (90572366363 / 4000000000000 : ℝ))
      (E := (cell12598 ⟨33, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (323965956337 / 390625000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (90572366363 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_34 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (3316043320593 / 4000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264313118613 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨34, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (3316043320593 / 4000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264313118613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_35 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82866905075639 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132158566453 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨35, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82866905075639 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132158566453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_36 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82832750973867 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264321144281 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨36, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82832750973867 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264321144281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_37 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (41399310339411 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264325153407 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨37, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (41399310339411 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264325153407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_38 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (82764514159967 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264329160739 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨38, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (82764514159967 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264329160739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_39 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (41365215693463 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264333166501 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨39, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (41365215693463 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264333166501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12599_20 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (20845521419437 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (7075408211 / 312500000000 : ℝ))
      (E := (cell12599 ⟨20, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (20845521419437 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (7075408211 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_21 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83347571017943 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264134623187 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨21, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83347571017943 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264134623187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_22 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41656540320829 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132069291511 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨22, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41656540320829 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132069291511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_23 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83278614515921 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132071313803 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨23, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83278614515921 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132071313803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_24 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83244172607931 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264146585659 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨24, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83244172607931 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264146585659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_25 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41604877442527 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264150577311 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨25, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41604877442527 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264150577311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_26 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (3327014452593 / 4000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264154605829 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨26, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (3327014452593 / 4000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264154605829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_27 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41570495932473 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264158615809 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨27, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41570495932473 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264158615809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_28 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83106646503283 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (113208130499 / 5000000000000 : ℝ))
      (E := (cell12599 ⟨28, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83106646503283 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (113208130499 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_29 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83072325197867 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132083295419 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨29, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83072325197867 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132083295419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_30 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83038027916893 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (45283412383 / 2000000000000 : ℝ))
      (E := (cell12599 ⟨30, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83038027916893 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (45283412383 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_31 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41501877314359 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264174579967 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨31, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41501877314359 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264174579967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_32 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82969505301861 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566044648031 / 25000000000000 : ℝ))
      (E := (cell12599 ⟨32, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82969505301861 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566044648031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_33 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82935279905001 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452836519739 / 20000000000000 : ℝ))
      (E := (cell12599 ⟨33, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82935279905001 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452836519739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_34 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (3316043136279 / 4000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264186601031 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨34, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (3316043136279 / 4000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264186601031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_35 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41433450388391 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566047650063 / 25000000000000 : ℝ))
      (E := (cell12599 ⟨35, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41433450388391 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566047650063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_36 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82832746983577 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (283024324657 / 12500000000000 : ℝ))
      (E := (cell12599 ⟨36, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82832746983577 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (283024324657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_37 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82798616996669 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264198592719 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨37, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82798616996669 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264198592719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_38 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (82764510785527 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264202645777 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨38, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (82764510785527 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264202645777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_39 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (20682607079943 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (22642066393 / 1000000000000 : ℝ))
      (E := (cell12599 ⟨39, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (20682607079943 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (22642066393 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

end BstLean.Part268
