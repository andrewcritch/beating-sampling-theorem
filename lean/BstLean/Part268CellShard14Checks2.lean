import BstLean.Part268CellShard14Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12700_40 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82696095365881 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125814772821 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨40, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82696095365881 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125814772821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_41 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (10332761382379 / 12500000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (56290838697 / 2500000000000 : ℝ))
      (E := (cell12700 ⟨41, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (10332761382379 / 12500000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (56290838697 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_42 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (2582128448903 / 3125000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562909390201 / 25000000000000 : ℝ))
      (E := (cell12700 ⟨42, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (2582128448903 / 3125000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562909390201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_43 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (4129707662689 / 5000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125820791807 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨43, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (4129707662689 / 5000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125820791807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_44 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (41280109848071 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251645556451 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨44, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (41280109848071 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251645556451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_45 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82526309662591 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (281456199467 / 12500000000000 : ℝ))
      (E := (cell12700 ⟨45, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82526309662591 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (281456199467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_46 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82492423123881 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (225165358231 / 10000000000000 : ℝ))
      (E := (cell12700 ⟨46, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82492423123881 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (225165358231 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_47 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (41229280025457 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251657573349 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨47, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (41229280025457 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251657573349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_48 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82424720414739 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251661625903 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨48, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82424720414739 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251661625903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_49 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82390904186549 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251665620029 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨49, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82390904186549 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251665620029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_50 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82357111337683 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (281458701541 / 12500000000000 : ℝ))
      (E := (cell12700 ⟨50, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82357111337683 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (281458701541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_51 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82323341839621 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (56291840007 / 2500000000000 : ℝ))
      (E := (cell12700 ⟨51, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82323341839621 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (56291840007 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_52 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (20572398915997 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125838820089 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨52, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (20572398915997 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125838820089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_53 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (10281984097819 / 12500000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125840805521 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨53, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (10281984097819 / 12500000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125840805521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_54 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82222173167219 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (11258428139 / 500000000000 : ℝ))
      (E := (cell12700 ⟨54, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82222173167219 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (11258428139 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_55 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82188496790037 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251689628059 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨55, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82188496790037 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251689628059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_56 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (16430968724639 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (281461708421 / 12500000000000 : ℝ))
      (E := (cell12700 ⟨56, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (16430968724639 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (281461708421 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_57 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (41060606819509 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562924405931 / 25000000000000 : ℝ))
      (E := (cell12700 ⟨57, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (41060606819509 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562924405931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_58 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82087606809971 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (112585083529 / 5000000000000 : ℝ))
      (E := (cell12700 ⟨58, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82087606809971 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (112585083529 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_59 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (16410804621731 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (450341137099 / 20000000000000 : ℝ))
      (E := (cell12700 ⟨59, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (16410804621731 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (450341137099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12701_40 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41348046347971 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281438356159 / 12500000000000 : ℝ))
      (E := (cell12701 ⟨40, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41348046347971 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281438356159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_41 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82662088691751 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251510846211 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨41, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82662088691751 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251510846211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_42 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41314054149927 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251514854531 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨42, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41314054149927 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251514854531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_43 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82594151490561 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251518873429 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨43, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82594151490561 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251518873429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_44 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82560218234331 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125761450943 / 50000000000000 : ℝ))
      (E := (cell12701 ⟨44, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82560218234331 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125761450943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_45 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (20631577125443 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (11257634399 / 500000000000 : ℝ))
      (E := (cell12701 ⟨45, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (20631577125443 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (11257634399 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_46 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82492422263639 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251530864537 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨46, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82492422263639 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251530864537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_47 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (16491711898167 / 20000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (112576745667 / 5000000000000 : ℝ))
      (E := (cell12701 ⟨47, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (16491711898167 / 20000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (112576745667 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_48 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (8242472015441 / 10000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562884726631 / 25000000000000 : ℝ))
      (E := (cell12701 ⟨48, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (8242472015441 / 10000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562884726631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_49 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41195452112779 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (28144286261 / 1250000000000 : ℝ))
      (E := (cell12701 ⟨49, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41195452112779 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (28144286261 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_50 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82357111675617 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125773447049 / 50000000000000 : ℝ))
      (E := (cell12701 ⟨50, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82357111675617 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125773447049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_51 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (8232334247607 / 10000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450310176731 / 20000000000000 : ℝ))
      (E := (cell12701 ⟨51, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (8232334247607 / 10000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450310176731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_52 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41144798299271 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450310985169 / 20000000000000 : ℝ))
      (E := (cell12701 ⟨52, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41144798299271 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450310985169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_53 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82255874014801 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251558899687 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨53, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82255874014801 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251558899687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_54 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (16444434939351 / 20000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562890730027 / 25000000000000 : ℝ))
      (E := (cell12701 ⟨54, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (16444434939351 / 20000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562890730027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_55 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82188498616451 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450313384943 / 20000000000000 : ℝ))
      (E := (cell12701 ⟨55, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82188498616451 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450313384943 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_56 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (513467785913 / 625000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251570909933 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨56, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (513467785913 / 625000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251570909933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_57 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82121216057967 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251574931127 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨57, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82121216057967 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251574931127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_58 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41043804762289 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (225157892521 / 10000000000000 : ℝ))
      (E := (cell12701 ⟨58, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41043804762289 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (225157892521 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_59 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41027013059257 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125791473591 / 50000000000000 : ℝ))
      (E := (cell12701 ⟨59, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41027013059257 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125791473591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12702_40 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (20674022506719 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251384208477 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨40, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (20674022506719 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251384208477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_41 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (41331043162653 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125694100089 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨41, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (41331043162653 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125694100089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_42 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (20657026558903 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125696101977 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨42, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (20657026558903 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125696101977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_43 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (41297074864053 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251396219 / 100000000000 : ℝ))
      (E := (cell12702 ⟨43, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (41297074864053 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251396219 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_44 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (41280108386623 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251400185457 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨44, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (41280108386623 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251400185457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_45 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (41263153670821 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450280843949 / 20000000000000 : ℝ))
      (E := (cell12702 ⟨45, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (41263153670821 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450280843949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_46 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82492421404049 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125704101353 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨46, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82492421404049 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125704101353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_47 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (20614639732843 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251412191509 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨47, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (20614639732843 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251412191509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_48 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82424719894661 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251416243207 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨48, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82424719894661 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251416243207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_49 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (8239090426511 / 10000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450284047571 / 20000000000000 : ℝ))
      (E := (cell12702 ⟨49, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (8239090426511 / 10000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450284047571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_50 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82357112014059 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251424232051 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨50, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82357112014059 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251424232051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_51 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82323343112991 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125714111637 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨51, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82323343112991 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125714111637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_52 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (20572399383383 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251432267817 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨52, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (20572399383383 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251432267817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_53 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (1645117504949 / 2000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251436244697 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨53, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (1645117504949 / 2000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251436244697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_54 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (41111088113327 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125720134421 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨54, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (41111088113327 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125720134421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_55 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82188500443193 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251444277857 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨55, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82188500443193 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251444277857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_56 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82154847869257 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125724134083 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨56, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82154847869257 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125724134083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_57 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (20530304619293 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251452295137 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨57, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (20530304619293 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251452295137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_58 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (16417522447881 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125728147839 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨58, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (16417522447881 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125728147839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_59 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82054029128559 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125730132797 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨59, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82054029128559 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125730132797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12703_40 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82696087358681 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (70351923891 / 3125000000000 : ℝ))
      (E := (cell12703 ⟨40, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82696087358681 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (70351923891 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_41 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (16532416791939 / 20000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251265551013 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨41, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (16532416791939 / 20000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251265551013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_42 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82628104172169 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251269550281 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨42, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82628104172169 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251269550281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_43 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (20648536991603 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (450254712303 / 20000000000000 : ℝ))
      (E := (cell12703 ⟨43, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (20648536991603 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (450254712303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_44 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41280107656443 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251277583691 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨44, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41280107656443 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251277583691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_45 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82526306182201 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251281556707 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨45, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82526306182201 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251281556707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_46 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82492420545113 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (140705349801 / 6250000000000 : ℝ))
      (E := (cell12703 ⟨46, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82492420545113 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (140705349801 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_47 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41229279186263 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125644792297 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨47, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41229279186263 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125644792297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_48 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (20606179908873 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251293577019 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨48, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (20606179908873 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251293577019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_49 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82390904305207 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125648785997 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨49, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82390904305207 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125648785997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_50 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82357112353009 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251301567207 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨50, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82357112353009 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251301567207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_51 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (5145208984399 / 6250000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125652809569 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨51, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (5145208984399 / 6250000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125652809569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_52 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41144799234479 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (281413700883 / 12500000000000 : ℝ))
      (E := (cell12703 ⟨52, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41144799234479 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (281413700883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_53 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82255876480499 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (112565679351 / 5000000000000 : ℝ))
      (E := (cell12703 ⟨53, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82255876480499 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (112565679351 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_54 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82222177756917 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125658807463 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨54, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82222177756917 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125658807463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_55 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82188502270263 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (450264325677 / 20000000000000 : ℝ))
      (E := (cell12703 ⟨55, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82188502270263 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (450264325677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_56 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (3286193999709 / 4000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (140707851489 / 6250000000000 : ℝ))
      (E := (cell12703 ⟨56, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (3286193999709 / 4000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (140707851489 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_57 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82121220896633 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125664828303 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨57, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82121220896633 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125664828303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_58 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82087614954453 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125666831821 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨58, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82087614954453 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125666831821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_59 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82054032138787 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (70354301273 / 3125000000000 : ℝ))
      (E := (cell12703 ⟨59, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82054032138787 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (70354301273 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12704_40 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82696084691359 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2198377849 / 97656250000 : ℝ))
      (E := (cell12704 ⟨40, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82696084691359 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2198377849 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_41 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (2066552039873 / 2500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125571478743 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨41, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (2066552039873 / 2500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125571478743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_42 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (20657025527381 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251146952309 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨42, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (20657025527381 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251146952309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_43 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (2064853655137 / 2500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225115095979 / 10000000000000 : ℝ))
      (E := (cell12704 ⟨43, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (2064853655137 / 2500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225115095979 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_44 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (20640053463313 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (450230995781 / 20000000000000 : ℝ))
      (E := (cell12704 ⟨44, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (20640053463313 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (450230995781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_45 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82526305023449 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140697434347 / 6250000000000 : ℝ))
      (E := (cell12704 ⟨45, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82526305023449 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140697434347 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_46 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82492419686829 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251162987981 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨46, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82492419686829 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251162987981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_47 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (10307319726787 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225116697477 / 10000000000000 : ℝ))
      (E := (cell12704 ⟨47, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (10307319726787 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225116697477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_48 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (10303089922113 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (450234193379 / 20000000000000 : ℝ))
      (E := (cell12704 ⟨48, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (10303089922113 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (450234193379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_49 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82390904345847 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251174962259 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨49, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82390904345847 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251174962259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_50 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82357112692467 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251178958547 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨50, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82357112692467 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251178958547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_51 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (10290418048531 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251183012243 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨51, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (10290418048531 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251183012243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_52 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (41144799702409 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251187002619 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨52, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (41144799702409 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251187002619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_53 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82255877713947 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225119098571 / 10000000000000 : ℝ))
      (E := (cell12704 ⟨53, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82255877713947 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225119098571 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_54 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82222179287543 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125597508719 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨54, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82222179287543 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125597508719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_55 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (4109425204883 / 5000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125599517701 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨55, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (4109425204883 / 5000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125599517701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_56 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (16430970423297 / 20000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225120303603 / 10000000000000 : ℝ))
      (E := (cell12704 ⟨56, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (16430970423297 / 20000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225120303603 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_57 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (1642424466327 / 2000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140700438471 / 6250000000000 : ℝ))
      (E := (cell12704 ⟨57, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (1642424466327 / 2000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140700438471 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_58 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (2052190441743 / 2500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140700689319 / 6250000000000 : ℝ))
      (E := (cell12704 ⟨58, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (2052190441743 / 2500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140700689319 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_59 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (205135087873 / 250000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225121501341 / 10000000000000 : ℝ))
      (E := (cell12704 ⟨59, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (205135087873 / 250000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225121501341 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12705_40 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (20674020506227 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251016384567 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨40, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (20674020506227 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251016384567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_41 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (4133103961549 / 5000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562755090207 / 25000000000000 : ℝ))
      (E := (cell12705 ⟨41, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (4133103961549 / 5000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562755090207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_42 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82628100047677 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251024351243 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨42, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82628100047677 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251024351243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_43 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82594144445311 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251028355007 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨43, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82594144445311 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251028355007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_44 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82560212394343 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (22510323711 / 1000000000000 : ℝ))
      (E := (cell12705 ⟨44, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82560212394343 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (22510323711 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_45 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41263151932693 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251036398279 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨45, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41263151932693 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251036398279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_46 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82492418829197 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125520188101 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨46, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82492418829197 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125520188101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_47 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82458557256683 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (45020888419 / 2000000000000 : ℝ))
      (E := (cell12705 ⟨47, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82458557256683 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (45020888419 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_48 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (16484943823779 / 20000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251048412837 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨48, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (16484943823779 / 20000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251048412837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_49 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82390904387031 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251052408649 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨49, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82390904387031 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251052408649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_50 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (5147319564527 / 6250000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (90042256243 / 4000000000000 : ℝ))
      (E := (cell12705 ⟨50, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (5147319564527 / 6250000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (90042256243 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_51 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (10290418128323 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562765100647 / 25000000000000 : ℝ))
      (E := (cell12705 ⟨51, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (10290418128323 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562765100647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_52 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41144800170557 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251064454481 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨52, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41144800170557 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251064454481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_53 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41127939473897 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251068440769 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨53, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41127939473897 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251068440769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_54 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82222180818533 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (22510724173 / 1000000000000 : ℝ))
      (E := (cell12705 ⟨54, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82222180818533 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (22510724173 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_55 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (10273563240673 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251076439807 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨55, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (10273563240673 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251076439807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_56 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82154854240537 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (112554022283 / 5000000000000 : ℝ))
      (E := (cell12705 ⟨56, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82154854240537 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (112554022283 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_57 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41060612868161 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562771107769 / 25000000000000 : ℝ))
      (E := (cell12705 ⟨57, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41060612868161 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562771107769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_58 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (10260952548151 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125544225617 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨58, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (10260952548151 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125544225617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_59 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41027019079899 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251092442813 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨59, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41027019079899 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251092442813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12706_40 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (2584252479979 / 3125000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (225089384859 / 10000000000000 : ℝ))
      (E := (cell12706 ⟨40, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (2584252479979 / 3125000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (225089384859 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_41 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41331038433937 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250897819811 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨41, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41331038433937 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250897819811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_42 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (20657024496657 / 25000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250901864673 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨42, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (20657024496657 / 25000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250901864673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_43 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41297071342951 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250905864807 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨43, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41297071342951 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250905864807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_44 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (82560210936159 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125454909559 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨44, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (82560210936159 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125454909559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_45 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (82526302708011 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125456922013 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨45, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (82526302708011 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125456922013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_46 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (82492417972217 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250917879257 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨46, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (82492417972217 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250917879257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_47 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16491711339937 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (90036874569 / 4000000000000 : ℝ))
      (E := (cell12706 ⟨47, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16491711339937 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (90036874569 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_48 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16484943772293 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (225092585591 / 10000000000000 : ℝ))
      (E := (cell12706 ⟨48, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16484943772293 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (225092585591 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_49 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41195452214379 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (140683115763 / 6250000000000 : ℝ))
      (E := (cell12706 ⟨49, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41195452214379 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (140683115763 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_50 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (10294639171613 / 12500000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281366731351 / 12500000000000 : ℝ))
      (E := (cell12706 ⟨50, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (10294639171613 / 12500000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281366731351 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_51 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (8232334566539 / 10000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250937908189 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨51, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (8232334566539 / 10000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250937908189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_52 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16457920255569 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125470951811 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨52, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16457920255569 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125470951811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_53 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (2056397004551 / 2500000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125472946571 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨53, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (2056397004551 / 2500000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125472946571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_54 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41111091174943 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250949873591 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨54, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41111091174943 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250949873591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_55 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16437701550687 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250953900701 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨55, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16437701550687 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250953900701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_56 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (1026935704561 / 1250000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (14068486949 / 625000000000 : ℝ))
      (E := (cell12706 ⟨56, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (1026935704561 / 1250000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (14068486949 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_57 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (1642424563131 / 2000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (90038476129 / 4000000000000 : ℝ))
      (E := (cell12706 ⟨57, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (1642424563131 / 2000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (90038476129 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_58 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16417524620183 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125482965017 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨58, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16417524620183 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125482965017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_59 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (82054041170579 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250969928947 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨59, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (82054041170579 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250969928947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12707_40 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82696076694619 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125385654723 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨40, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82696076694619 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125385654723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_41 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82662074505603 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (450155066887 / 20000000000000 : ℝ))
      (E := (cell12707 ⟨41, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82662074505603 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (450155066887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_42 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82628095926377 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250779316217 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨42, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82628095926377 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250779316217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_43 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (16518828185451 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250783312733 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨43, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (16518828185451 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250783312733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_44 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (825602094787 / 1000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250787322961 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨44, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (825602094787 / 1000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250787322961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_45 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (3301052062053 / 4000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125395672829 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨45, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (3301052062053 / 4000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125395672829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_46 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (8249241711589 / 10000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250795379369 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨46, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (8249241711589 / 10000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250795379369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_47 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41229278071651 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250799363507 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨47, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41229278071651 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250799363507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_48 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (16484943720923 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250803355049 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨48, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (16484943720923 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250803355049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_49 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (20597726117757 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (450161470379 / 20000000000000 : ℝ))
      (E := (cell12707 ⟨49, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (20597726117757 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (450161470379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_50 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82357113713883 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250811351729 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨50, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82357113713883 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250811351729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_51 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (20580836576167 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (281351919003 / 12500000000000 : ℝ))
      (E := (cell12707 ⟨51, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (20580836576167 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (281351919003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_52 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82289602215011 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (140676213067 / 6250000000000 : ℝ))
      (E := (cell12707 ⟨52, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82289602215011 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (140676213067 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_53 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (16451176283337 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125411700943 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨53, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (16451176283337 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125411700943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_54 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82222183881601 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250827386313 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨54, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82222183881601 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250827386313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_55 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41094254790907 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (450166283617 / 20000000000000 : ℝ))
      (E := (cell12707 ⟨55, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41094254790907 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (450166283617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_56 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41077429244757 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250835434571 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨56, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41077429244757 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250835434571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_57 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41060615288517 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (140677464499 / 6250000000000 : ℝ))
      (E := (cell12707 ⟨57, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41060615288517 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (140677464499 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_58 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41043812908421 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125421703167 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨58, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41043812908421 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125421703167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_59 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (10256755522693 / 12500000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250847412617 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨59, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (10256755522693 / 12500000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250847412617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12708_40 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (82696074030781 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250648884633 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨40, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (82696074030781 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250648884633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_41 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (41331036072083 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250652845931 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨41, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (41331036072083 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250652845931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_42 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (20657023466731 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250656882259 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨42, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (20657023466731 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250656882259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_43 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (82594139169369 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250660875243 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨43, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (82594139169369 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250660875243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_44 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (16512041604393 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (225066488263 / 10000000000000 : ℝ))
      (E := (cell12708 ⟨44, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (16512041604393 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (225066488263 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_45 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (82526300395327 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250668903177 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨45, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (82526300395327 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250668903177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_46 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (41246208130107 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (112533643827 / 5000000000000 : ℝ))
      (E := (cell12708 ⟨46, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (41246208130107 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (112533643827 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_47 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (16491711117507 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250676918797 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨47, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (16491711117507 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250676918797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_48 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (16484943669669 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250680910257 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨48, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (16484943669669 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250680910257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_49 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (82390904513841 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250684907711 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨49, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (82390904513841 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250684907711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_50 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (82357114055369 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (56267222721 / 2500000000000 : ℝ))
      (E := (cell12708 ⟨50, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (82357114055369 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (56267222721 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_51 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (2572604592013 / 3125000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250692911117 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨51, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (2572604592013 / 3125000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250692911117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_52 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (20572400788153 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250696911803 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨52, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (20572400788153 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250696911803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_53 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (5140992665733 / 6250000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562675226987 / 25000000000000 : ℝ))
      (E := (cell12708 ⟨53, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (5140992665733 / 6250000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562675226987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_54 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (1027777317671 / 1250000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125352477733 / 50000000000000 : ℝ))
      (E := (cell12708 ⟨54, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (1027777317671 / 1250000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125352477733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_55 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (82188511410519 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250708932861 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨55, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (82188511410519 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250708932861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_56 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (82154860614439 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250712954729 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨56, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (82154860614439 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250712954729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_57 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (20530308249443 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250716958209 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨57, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (20530308249443 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250716958209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_58 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (20521907133247 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250720939307 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨58, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (20521907133247 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250720939307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_59 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (41027023596347 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250724953019 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨59, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (41027023596347 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250724953019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12709_40 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82696071367813 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450105279581 / 20000000000000 : ℝ))
      (E := (cell12709 ⟨40, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82696071367813 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450105279581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_41 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82662069783563 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225053041307 / 10000000000000 : ℝ))
      (E := (cell12709 ⟨41, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82662069783563 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225053041307 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_42 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (20657022952067 / 25000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225053444521 / 10000000000000 : ℝ))
      (E := (cell12709 ⟨42, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (20657022952067 / 25000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225053444521 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_43 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82594137412243 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250538434699 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨43, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82594137412243 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250538434699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_44 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (16512041313191 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125271219641 / 50000000000000 : ℝ))
      (E := (cell12709 ⟨44, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (16512041313191 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125271219641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_45 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82526299240017 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250546457717 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨45, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82526299240017 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250546457717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_46 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (8249241540519 / 10000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250550429657 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨46, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (8249241540519 / 10000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250550429657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_47 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (1288414922381 / 1562500000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250554471181 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨47, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (1288414922381 / 1562500000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250554471181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_48 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82424718092653 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250558462599 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨48, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82424718092653 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250558462599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_49 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82390904557197 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250562460697 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨49, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82390904557197 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250562460697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_50 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41178557198681 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125283231579 / 50000000000000 : ℝ))
      (E := (cell12709 ⟨50, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41178557198681 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125283231579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_51 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (16464669516927 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250570467453 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨51, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (16464669516927 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250570467453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_52 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82289604090647 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562643617711 / 25000000000000 : ℝ))
      (E := (cell12709 ⟨52, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82289604090647 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562643617711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_53 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82255883887171 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250578470379 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨53, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82255883887171 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250578470379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_54 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (2055554673653 / 2500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (90023300879 / 4000000000000 : ℝ))
      (E := (cell12709 ⟨54, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (2055554673653 / 2500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (90023300879 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_55 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82188513239551 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (35165414127 / 1562500000000 : ℝ))
      (E := (cell12709 ⟨55, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82188513239551 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (35165414127 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_56 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (16430972547931 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250590531439 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨56, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (16430972547931 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250590531439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_57 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41060617709383 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450118908209 / 20000000000000 : ℝ))
      (E := (cell12709 ⟨57, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41060617709383 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450118908209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_58 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41043815624677 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250598528951 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨58, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41043815624677 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250598528951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_59 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41027025102013 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125301275077 / 50000000000000 : ℝ))
      (E := (cell12709 ⟨59, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41027025102013 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125301275077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12710_40 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20674017176429 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250404025509 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨40, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20674017176429 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250404025509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_41 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82662067423793 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (140650502241 / 6250000000000 : ℝ))
      (E := (cell12710 ⟨41, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82662067423793 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (140650502241 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_42 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82628089750409 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250412005073 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨42, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82628089750409 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250412005073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_43 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82594135655879 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125208024961 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨43, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82594135655879 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125208024961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_44 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82560205110669 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125210025881 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨44, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82560205110669 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125210025881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_45 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (41263149042697 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125212034073 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨45, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (41263149042697 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125212034073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_46 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82492414550817 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562607009681 / 25000000000000 : ℝ))
      (E := (cell12710 ⟨46, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82492414550817 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562607009681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_47 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82458554477847 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (281304009947 / 12500000000000 : ℝ))
      (E := (cell12710 ⟨47, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82458554477847 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (281304009947 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_48 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (4121235891877 / 5000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250436071011 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨48, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (4121235891877 / 5000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250436071011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_49 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (10298863075137 / 12500000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250440069813 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨49, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (10298863075137 / 12500000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250440069813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_50 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82357114739861 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250444073667 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨50, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82357114739861 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250444073667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_51 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20580837056331 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125224040021 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨51, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20580837056331 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125224040021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_52 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20572401257279 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250452086199 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨52, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20572401257279 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250452086199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_53 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82255885123011 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (450091217837 / 20000000000000 : ℝ))
      (E := (cell12710 ⟨53, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82255885123011 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (450091217837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_54 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20555547119731 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250460085837 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨54, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20555547119731 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250460085837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_55 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82188515068909 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562616018197 / 25000000000000 : ℝ))
      (E := (cell12710 ⟨55, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82188515068909 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562616018197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_56 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (41077432432581 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250468105579 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨56, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (41077432432581 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250468105579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_57 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (16424247568003 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250472121347 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨57, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (16424247568003 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250472121347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_58 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82087633965939 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125238058049 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨58, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82087633965939 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125238058049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_59 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82054053215543 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125240072413 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨59, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82054053215543 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125240072413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12711_40 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (10337008255561 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250281649951 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨40, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (10337008255561 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250281649951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_41 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82662065064857 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125142827757 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨41, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82662065064857 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125142827757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_42 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41314043846673 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125144839719 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨42, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41314043846673 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125144839719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_43 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41297066950137 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125146831047 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨43, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41297066950137 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125146831047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_44 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41280101828053 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (225029766123 / 10000000000000 : ℝ))
      (E := (cell12711 ⟨44, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41280101828053 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (225029766123 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_45 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82526296931459 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125150837799 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨45, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82526296931459 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125150837799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_46 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (16498482739419 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250305703741 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨46, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (16498482739419 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250305703741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_47 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (3298342156957 / 4000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250309685069 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨47, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (3298342156957 / 4000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250309685069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_48 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (16484943516601 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125156838279 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨48, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (16484943516601 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125156838279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_49 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82390904645537 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125158838051 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨49, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82390904645537 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125158838051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_50 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41178557541433 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125160840693 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨50, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41178557541433 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125160840693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_51 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82323348866483 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250325689877 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨51, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82323348866483 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250325689877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_52 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82289605968019 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562582424709 / 25000000000000 : ℝ))
      (E := (cell12711 ⟨52, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82289605968019 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562582424709 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_53 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (329023545437 / 400000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250333705309 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨53, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (329023545437 / 400000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250333705309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_54 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (8222219001209 / 10000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125168853067 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨54, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (8222219001209 / 10000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125168853067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_55 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41094258449297 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125170878521 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨55, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41094258449297 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125170878521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_56 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82154866990959 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250345736273 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨56, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82154866990959 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250345736273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_57 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41060620130759 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281293719783 / 12500000000000 : ℝ))
      (E := (cell12711 ⟨57, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41060620130759 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281293719783 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_58 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82087636682743 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (28129421999 / 1250000000000 : ℝ))
      (E := (cell12711 ⟨58, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82087636682743 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (28129421999 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_59 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82054056227243 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250357737039 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨59, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82054056227243 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250357737039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12712_40 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (8269606338413 / 10000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125079664989 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨40, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (8269606338413 / 10000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125079664989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_41 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82662062706753 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (112508166541 / 5000000000000 : ℝ))
      (E := (cell12712 ⟨41, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82662062706753 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (112508166541 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_42 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (2065702140927 / 2500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (450033470143 / 20000000000000 : ℝ))
      (E := (cell12712 ⟨42, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (2065702140927 / 2500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (450033470143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_43 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82594132145429 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (450034266007 / 20000000000000 : ℝ))
      (E := (cell12712 ⟨43, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82594132145429 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (450034266007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_44 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (20640050550567 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562543831631 / 25000000000000 : ℝ))
      (E := (cell12712 ⟨44, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (20640050550567 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562543831631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_45 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82526295778211 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (112508966947 / 5000000000000 : ℝ))
      (E := (cell12712 ⟨45, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82526295778211 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (112508966947 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_46 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (3299696513761 / 4000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250183365819 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨46, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (3299696513761 / 4000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250183365819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_47 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41229276685309 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250187346573 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨47, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41229276685309 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250187346573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_48 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82424717329049 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (35159239659 / 1562500000000 : ℝ))
      (E := (cell12712 ⟨48, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82424717329049 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (35159239659 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_49 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (2059772617263 / 2500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250195338523 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨49, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (2059772617263 / 2500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250195338523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_50 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41178557713189 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (140637459081 / 6250000000000 : ℝ))
      (E := (cell12712 ⟨50, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41178557713189 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (140637459081 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_51 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (5145209344257 / 6250000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (450040671193 / 20000000000000 : ℝ))
      (E := (cell12712 ⟨51, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (5145209344257 / 6250000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (450040671193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_52 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82289606907357 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125103683893 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨52, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82289606907357 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125103683893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_53 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82255887595887 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250211377807 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨53, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82255887595887 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250211377807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_54 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82222191545617 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125107691433 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨54, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82222191545617 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125107691433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_55 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41094259364303 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562554844897 / 25000000000000 : ℝ))
      (E := (cell12712 ⟨55, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41094259364303 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562554844897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_56 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82154869117047 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250223423521 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨56, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82154869117047 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250223423521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_57 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82121242683277 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125113696323 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨57, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82121242683277 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125113696323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_58 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41043819699883 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562557850311 / 25000000000000 : ℝ))
      (E := (cell12712 ⟨58, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41043819699883 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562557850311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_59 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41027029619563 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125117722591 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨59, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41027029619563 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125117722591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12713_40 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (41348030362321 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250037006843 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨40, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (41348030362321 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250037006843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_41 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82662060349483 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250041003 / 100000000000 : ℝ))
      (E := (cell12713 ⟨41, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82662060349483 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250041003 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_42 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82628083581611 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281255627363 / 12500000000000 : ℝ))
      (E := (cell12713 ⟨42, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82628083581611 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281255627363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_43 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (16518826078269 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (140628065859 / 6250000000000 : ℝ))
      (E := (cell12713 ⟨43, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (16518826078269 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (140628065859 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_44 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (2580006273411 / 3125000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250053047651 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨44, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (2580006273411 / 3125000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250053047651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_45 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82526294625651 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562514264543 / 25000000000000 : ℝ))
      (E := (cell12713 ⟨45, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82526294625651 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562514264543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_46 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (20623102997901 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (7031440703 / 312500000000 : ℝ))
      (E := (cell12713 ⟨46, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (20623102997901 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (7031440703 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_47 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (3298342112717 / 4000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (225006506409 / 10000000000000 : ℝ))
      (E := (cell12713 ⟨47, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (3298342112717 / 4000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (225006506409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_48 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82424717075671 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562517263967 / 25000000000000 : ℝ))
      (E := (cell12713 ⟨48, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82424717075671 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562517263967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_49 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (41195452368023 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250073057077 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨49, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (41195452368023 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250073057077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_50 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (16471423154079 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125038532701 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨50, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (16471423154079 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125038532701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_51 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (20580837537553 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250081078307 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨51, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (20580837537553 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250081078307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_52 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (10286200980891 / 12500000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562521273263 / 25000000000000 : ℝ))
      (E := (cell12713 ⟨52, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (10286200980891 / 12500000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562521273263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_53 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82255888832921 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250089106681 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨53, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82255888832921 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250089106681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_54 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82222193079507 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250093116033 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨54, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82222193079507 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250093116033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_55 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82188520558943 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250097117733 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨55, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82188520558943 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250097117733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_56 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (3286194849737 / 4000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (11250505541 / 500000000000 : ℝ))
      (E := (cell12713 ⟨56, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (3286194849737 / 4000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (11250505541 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_57 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82121245105289 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125052571397 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨57, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82121245105289 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125052571397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_58 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82087642117009 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562527274811 / 25000000000000 : ℝ))
      (E := (cell12713 ⟨58, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82087642117009 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562527274811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_59 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82054062251193 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (140632071929 / 6250000000000 : ℝ))
      (E := (cell12713 ⟨59, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82054062251193 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (140632071929 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12714_40 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82696058066023 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (70309835603 / 3125000000000 : ℝ))
      (E := (cell12714 ⟨40, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82696058066023 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (70309835603 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_41 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (16532411598609 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249918789603 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨41, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (16532411598609 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249918789603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_42 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (41314040763469 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562480685701 / 25000000000000 : ℝ))
      (E := (cell12714 ⟨42, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (41314040763469 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562480685701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_43 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (4129706431901 / 5000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124963387203 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨43, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (4129706431901 / 5000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124963387203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_44 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (2064004982419 / 2500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124965382883 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨44, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (2064004982419 / 2500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124965382883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_45 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (5157893342111 / 6250000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249934774433 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨45, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (5157893342111 / 6250000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249934774433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_46 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (16498482227967 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124969399471 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨46, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (16498482227967 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124969399471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_47 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82458552265847 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124971389353 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨47, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82458552265847 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124971389353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_48 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (10303089602859 / 12500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (281243346337 / 12500000000000 : ℝ))
      (E := (cell12714 ⟨48, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (10303089602859 / 12500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (281243346337 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_49 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82390904782113 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249950831767 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨49, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82390904782113 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249950831767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_50 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (41178558057459 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249954782719 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨50, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (41178558057459 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249954782719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_51 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (4116167539639 / 5000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124979398949 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨51, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (4116167539639 / 5000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124979398949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_52 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82289608787333 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249962815603 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨52, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82289608787333 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249962815603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_53 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (41127945035177 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249966832877 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨53, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (41127945035177 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249966832877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_54 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82222194613759 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124985423279 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨54, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82222194613759 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124985423279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_55 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (41094261194803 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (281246856659 / 12500000000000 : ℝ))
      (E := (cell12714 ⟨55, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (41094261194803 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (281246856659 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_56 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (41077436685047 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562494712359 / 25000000000000 : ℝ))
      (E := (cell12714 ⟨56, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (41077436685047 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562494712359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_57 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82121247527557 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249982831261 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨57, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82121247527557 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249982831261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_58 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82087644834469 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124993426961 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨58, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82087644834469 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124993426961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_59 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82054065263443 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249990854089 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨59, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82054065263443 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249990854089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12715_40 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82696055408273 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124896263669 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨40, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82696055408273 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124896263669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_41 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (258318923867 / 312500000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224979651431 / 10000000000000 : ℝ))
      (E := (cell12715 ⟨41, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (258318923867 / 312500000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224979651431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_42 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (4131403973653 / 5000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449960104483 / 20000000000000 : ℝ))
      (E := (cell12715 ⟨42, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (4131403973653 / 5000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449960104483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_43 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41297063442727 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (56245113771 / 2500000000000 : ℝ))
      (E := (cell12715 ⟨43, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41297063442727 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (56245113771 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_44 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82560197845091 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249808539713 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨44, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82560197845091 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249808539713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_45 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82526292322589 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (281226568323 / 12500000000000 : ℝ))
      (E := (cell12715 ⟨45, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82526292322589 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (281226568323 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_46 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (16498482057743 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224981656999 / 10000000000000 : ℝ))
      (E := (cell12715 ⟨46, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (16498482057743 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224981656999 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_47 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41229275857191 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124910274669 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨47, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41229275857191 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124910274669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_48 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82424716570649 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249824541601 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨48, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82424716570649 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249824541601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_49 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82390904828721 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (70307142021 / 3125000000000 : ℝ))
      (E := (cell12715 ⟨49, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82390904828721 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (70307142021 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_50 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82357116459947 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249832556231 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨50, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82357116459947 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249832556231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_51 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82323351435819 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449967314749 / 20000000000000 : ℝ))
      (E := (cell12715 ⟨51, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82323351435819 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449967314749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_52 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (20572402431993 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224984059447 / 10000000000000 : ℝ))
      (E := (cell12715 ⟨52, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (20572402431993 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224984059447 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_53 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (10281986413523 / 12500000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (44996892309 / 2000000000000 : ℝ))
      (E := (cell12715 ⟨53, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (10281986413523 / 12500000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (44996892309 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_54 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (20555549037093 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562462143611 / 25000000000000 : ℝ))
      (E := (cell12715 ⟨54, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (20555549037093 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562462143611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_55 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (16437704844119 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (70307893319 / 3125000000000 : ℝ))
      (E := (cell12715 ⟨55, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (16437704844119 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (70307893319 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_56 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (20538718874263 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124928294053 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨56, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (20538718874263 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124928294053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_57 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41060624975039 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449972127099 / 20000000000000 : ℝ))
      (E := (cell12715 ⟨57, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41060624975039 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449972127099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_58 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82087647552149 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449972921221 / 20000000000000 : ℝ))
      (E := (cell12715 ⟨58, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82087647552149 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449972921221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_59 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (20513517068969 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562467153513 / 25000000000000 : ℝ))
      (E := (cell12715 ⟨59, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (20513517068969 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562467153513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12716_40 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82696052751391 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249670312221 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨40, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82696052751391 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249670312221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_41 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82662053282667 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (14060464709 / 625000000000 : ℝ))
      (E := (cell12716 ⟨41, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82662053282667 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (14060464709 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_42 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (41314038709989 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281209794717 / 12500000000000 : ℝ))
      (E := (cell12716 ⟨42, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (41314038709989 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281209794717 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_43 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82594125133647 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124841162113 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨43, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82594125133647 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124841162113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_44 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (2580006137317 / 3125000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124843184747 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨44, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (2580006137317 / 3125000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124843184747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_45 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (10315786396511 / 12500000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (224969037463 / 10000000000000 : ℝ))
      (E := (cell12716 ⟨45, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (10315786396511 / 12500000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (224969037463 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_46 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (41246204719123 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249694338101 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨46, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (41246204719123 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249694338101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_47 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82458551163531 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (140606148499 / 6250000000000 : ℝ))
      (E := (cell12716 ⟨47, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82458551163531 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (140606148499 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_48 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (16484943263801 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (112485118429 / 5000000000000 : ℝ))
      (E := (cell12716 ⟨48, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (16484943263801 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (112485118429 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_49 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (2574715777371 / 3125000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (35151662073 / 1562500000000 : ℝ))
      (E := (cell12716 ⟨49, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (2574715777371 / 3125000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (35151662073 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_50 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82357116805481 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (112485519297 / 5000000000000 : ℝ))
      (E := (cell12716 ⟨50, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82357116805481 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (112485519297 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_51 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (41161676039663 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249714405849 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨51, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (41161676039663 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249714405849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_52 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (20572402667261 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249718370623 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨52, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (20572402667261 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249718370623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_53 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82255892546411 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124861197673 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨53, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82255892546411 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124861197673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_54 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82222197683347 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (562431604461 / 25000000000000 : ℝ))
      (E := (cell12716 ⟨54, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82222197683347 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (562431604461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_55 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (8218852605191 / 10000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249730434743 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨55, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (8218852605191 / 10000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249730434743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_56 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (821548776243 / 1000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124867221229 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨56, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (821548776243 / 1000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124867221229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_57 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (41060626186427 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249738437199 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨57, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (41060626186427 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249738437199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_58 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82087650270047 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249742414967 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨58, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82087650270047 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249742414967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_59 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82054071288491 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249746430753 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨59, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82054071288491 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249746430753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12717_40 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41348025047689 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124774076347 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨40, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41348025047689 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124774076347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_41 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (3306482037149 / 4000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (44991043789 / 2000000000000 : ℝ))
      (E := (cell12717 ⟨41, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (3306482037149 / 4000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (44991043789 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_42 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82628075367691 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (89982247599 / 4000000000000 : ℝ))
      (E := (cell12717 ⟨42, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82628075367691 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (89982247599 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_43 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82594123382599 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449912030677 / 20000000000000 : ℝ))
      (E := (cell12717 ⟨43, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82594123382599 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449912030677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_44 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (1032002436799 / 1250000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449912839253 / 20000000000000 : ℝ))
      (E := (cell12717 ⟨44, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (1032002436799 / 1250000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449912839253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_45 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82526290022273 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (281196024963 / 12500000000000 : ℝ))
      (E := (cell12717 ⟨45, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82526290022273 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (281196024963 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_46 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41246204294213 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124786110529 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨46, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41246204294213 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124786110529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_47 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41229275306647 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249576199733 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨47, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41229275306647 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249576199733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_48 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41212358033969 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249580192699 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨48, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41212358033969 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249580192699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_49 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82390904923563 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (44991683957 / 2000000000000 : ℝ))
      (E := (cell12717 ⟨49, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82390904923563 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (44991683957 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_50 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (514731982197 / 625000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249588212863 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨50, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (514731982197 / 625000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249588212863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_51 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82323352723303 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (562398058801 / 25000000000000 : ℝ))
      (E := (cell12717 ⟨51, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82323352723303 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (562398058801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_52 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82289611610549 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449919240619 / 20000000000000 : ℝ))
      (E := (cell12717 ⟨52, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82289611610549 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449919240619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_53 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (16451178757007 / 20000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249600231621 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨53, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (16451178757007 / 20000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249600231621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_54 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82222199218683 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124802129303 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨54, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82222199218683 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124802129303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_55 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82188527883551 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249608221573 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨55, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82188527883551 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249608221573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_56 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41077439875919 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249612235119 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨56, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41077439875919 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249612235119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_57 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (20530313698971 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249616236373 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨57, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (20530313698971 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249616236373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_58 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82087652988163 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (562405070127 / 25000000000000 : ℝ))
      (E := (cell12717 ⟨58, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82087652988163 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (562405070127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_59 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (8205407430129 / 10000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249624244997 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨59, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (8205407430129 / 10000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249624244997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12718_40 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82696047440233 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (56235651219 / 2500000000000 : ℝ))
      (E := (cell12718 ⟨40, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82696047440233 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (56235651219 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_41 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (16532409715123 / 20000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (112471501117 / 5000000000000 : ℝ))
      (E := (cell12718 ⟨41, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (16532409715123 / 20000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (112471501117 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_42 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (413140366581 / 500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249434019131 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨42, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (413140366581 / 500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249434019131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_43 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (8259412163231 / 10000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249438038319 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨43, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (8259412163231 / 10000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249438038319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_44 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (41280096747209 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (281180259859 / 12500000000000 : ℝ))
      (E := (cell12718 ⟨44, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (41280096747209 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (281180259859 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_45 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (10315786109143 / 12500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (89977843227 / 4000000000000 : ℝ))
      (E := (cell12718 ⟨45, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (10315786109143 / 12500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (89977843227 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_46 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (10311550967407 / 12500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (140590627637 / 6250000000000 : ℝ))
      (E := (cell12718 ⟨46, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (10311550967407 / 12500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (140590627637 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_47 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (8245855006367 / 10000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249454079499 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨47, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (8245855006367 / 10000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249454079499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_48 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (10303089477181 / 12500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249458072897 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨48, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (10303089477181 / 12500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249458072897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_49 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (16478180994359 / 20000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249462079167 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨49, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (16478180994359 / 20000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249462079167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_50 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (5147319843629 / 6250000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (449893219197 / 20000000000000 : ℝ))
      (E := (cell12718 ⟨50, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (5147319843629 / 6250000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (449893219197 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_51 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82323353367749 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249470120817 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨51, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82323353367749 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249470120817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_52 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82289612552487 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249474091887 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨52, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82289612552487 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249474091887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_53 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82255895024057 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562369531069 / 25000000000000 : ℝ))
      (E := (cell12718 ⟨53, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82255895024057 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562369531069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_54 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (4111110037719 / 5000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (224948209673 / 10000000000000 : ℝ))
      (E := (cell12718 ⟨54, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (4111110037719 / 5000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (224948209673 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_55 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (20547132428879 / 25000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249486124007 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨55, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (20547132428879 / 25000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249486124007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_56 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (41077440939833 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124745071733 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨56, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (41077440939833 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124745071733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_57 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (2566289288099 / 3125000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562373537829 / 25000000000000 : ℝ))
      (E := (cell12718 ⟨57, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (2566289288099 / 3125000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562373537829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_58 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (41043827853249 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249498143557 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨58, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (41043827853249 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249498143557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_59 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82054077314271 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124751057991 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨59, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82054077314271 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124751057991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12719_40 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (20674011196489 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249303941669 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨40, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (20674011196489 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249303941669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_41 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82662046223337 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (449861593931 / 20000000000000 : ℝ))
      (E := (cell12719 ⟨41, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82662046223337 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (449861593931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_42 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82628071265503 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124655981399 / 50000000000000 : ℝ))
      (E := (cell12719 ⟨42, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82628071265503 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124655981399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_43 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82594119882779 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249315979029 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨43, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82594119882779 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249315979029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_44 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (41280096022819 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (281164994809 / 12500000000000 : ℝ))
      (E := (cell12719 ⟨44, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (41280096022819 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (281164994809 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_45 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (825262877247 / 1000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562330989669 / 25000000000000 : ℝ))
      (E := (cell12719 ⟨45, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (825262877247 / 1000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562330989669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_46 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (16498481378147 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124663989087 / 50000000000000 : ℝ))
      (E := (cell12719 ⟨46, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (16498481378147 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124663989087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_47 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82458549514659 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224933195637 / 10000000000000 : ℝ))
      (E := (cell12719 ⟨47, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82458549514659 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224933195637 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_48 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (16484943113507 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249336009173 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨48, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (16484943113507 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249336009173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_49 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82390905020569 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (112466997883 / 5000000000000 : ℝ))
      (E := (cell12719 ⟨49, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82390905020569 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (112466997883 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_50 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82357117845113 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124671988161 / 50000000000000 : ℝ))
      (E := (cell12719 ⟨50, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82357117845113 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124671988161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_51 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82323354012663 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562337000921 / 25000000000000 : ℝ))
      (E := (cell12719 ⟨51, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82323354012663 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562337000921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_52 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82289613494857 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249351977969 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨52, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82289613494857 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249351977969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_53 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (3290235850539 / 4000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249356014257 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨53, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (3290235850539 / 4000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249356014257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_54 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (41111101145219 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (449871998259 / 20000000000000 : ℝ))
      (E := (cell12719 ⟨54, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (41111101145219 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (449871998259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_55 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82188531547807 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249364023839 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨55, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82188531547807 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249364023839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_56 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82154884007783 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249368049249 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨56, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82154884007783 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249368049249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_57 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (16424251928541 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249372004583 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨57, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (16424251928541 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249372004583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_58 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82087658425051 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249376063287 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨58, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82087658425051 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249376063287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_59 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (41027040163717 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249380043709 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨59, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (41027040163717 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249380043709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12720_40 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82696042132547 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249181890171 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨40, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82696042132547 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249181890171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_41 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82662043871889 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249185855081 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨41, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82662043871889 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249185855081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_42 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82628069215601 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (281148737923 / 12500000000000 : ℝ))
      (E := (cell12720 ⟨42, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82628069215601 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (281148737923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_43 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82594118134007 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124596958347 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨43, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82594118134007 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124596958347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_44 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (4128009529879 / 5000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249197893909 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨44, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (4128009529879 / 5000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249197893909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_45 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41263143288471 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (89968075703 / 4000000000000 : ℝ))
      (E := (cell12720 ⟨45, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41263143288471 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (89968075703 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_46 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (5155775377679 / 6250000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249205911223 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨46, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (5155775377679 / 6250000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249205911223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_47 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41229274483131 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (112460494463 / 5000000000000 : ℝ))
      (E := (cell12720 ⟨47, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41229274483131 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (112460494463 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_48 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82424715318199 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249213942591 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨48, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82424715318199 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249213942591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_49 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82390905069883 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (281152243907 / 12500000000000 : ℝ))
      (E := (cell12720 ⟨49, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82390905069883 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (281152243907 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_50 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82357118192667 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249221912859 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨50, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82357118192667 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249221912859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_51 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41161677329023 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562306485703 / 25000000000000 : ℝ))
      (E := (cell12720 ⟨51, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41161677329023 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562306485703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_52 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82289614437661 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (224922992037 / 10000000000000 : ℝ))
      (E := (cell12720 ⟨52, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82289614437661 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (224922992037 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_53 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82255897503291 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124616980309 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨53, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82255897503291 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124616980309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_54 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82222203826857 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249237942301 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨54, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82222203826857 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249237942301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_55 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82188533380423 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249241980173 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨55, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82188533380423 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249241980173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_56 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (8215488613619 / 10000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562311488117 / 25000000000000 : ℝ))
      (E := (cell12720 ⟨56, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (8215488613619 / 10000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562311488117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_57 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (1283144719789 / 1562500000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249249973621 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨57, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (1283144719789 / 1562500000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249249973621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_58 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41043830571911 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249253980527 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨58, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41043830571911 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249253980527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_59 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (4102704167039 / 5000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124628984491 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨59, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (4102704167039 / 5000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124628984491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12721_40 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (16539207896001 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249059835519 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨40, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (16539207896001 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249059835519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_41 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82662041521273 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124531927467 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨41, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82662041521273 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124531927467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_42 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82628067166493 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (224906784089 / 10000000000000 : ℝ))
      (E := (cell12721 ⟨42, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82628067166493 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (224906784089 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_43 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (10324264548249 / 12500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249071851317 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨43, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (10324264548249 / 12500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249071851317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_44 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82560189150243 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (17570905353 / 781250000000 : ℝ))
      (E := (cell12721 ⟨44, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82560189150243 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (17570905353 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_45 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82526285429869 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249079882371 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨45, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82526285429869 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249079882371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_46 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82492405195641 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (281135487529 / 12500000000000 : ℝ))
      (E := (cell12721 ⟨46, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82492405195641 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (281135487529 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_47 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82458548418477 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249087878169 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨47, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82458548418477 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249087878169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_48 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82424715069439 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (17571030259 / 781250000000 : ℝ))
      (E := (cell12721 ⟨48, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82424715069439 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (17571030259 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_49 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82390905119737 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (224909588307 / 10000000000000 : ℝ))
      (E := (cell12721 ⟨49, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82390905119737 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (224909588307 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_50 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (3294284741629 / 4000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124549952799 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨50, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (3294284741629 / 4000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124549952799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_51 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41161677651949 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249103879191 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨51, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41161677651949 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249103879191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_52 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82289615380897 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124553959547 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨52, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82289615380897 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124553959547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_53 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41127949371751 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562277976077 / 25000000000000 : ℝ))
      (E := (cell12721 ⟨53, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41127949371751 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562277976077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_54 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82222205363637 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249115949749 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨54, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82222205363637 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249115949749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_55 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (20547133803341 / 25000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249119933907 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨55, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (20547133803341 / 25000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249119933907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_56 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (16430977652977 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (8996495649 / 400000000000 : ℝ))
      (E := (cell12721 ⟨56, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (16430977652977 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (8996495649 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_57 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82121264490541 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562281985033 / 25000000000000 : ℝ))
      (E := (cell12721 ⟨57, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82121264490541 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562281985033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_58 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (8208766386281 / 10000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (44982639089 / 2000000000000 : ℝ))
      (E := (cell12721 ⟨58, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (8208766386281 / 10000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (44982639089 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_59 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82054086354309 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449827190199 / 20000000000000 : ℝ))
      (E := (cell12721 ⟨59, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82054086354309 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449827190199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12722_40 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (8269603682833 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248937836463 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨40, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (8269603682833 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248937836463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_41 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82662039171487 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (281117731459 / 12500000000000 : ℝ))
      (E := (cell12722 ⟨41, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82662039171487 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (281117731459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_42 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (4131403255909 / 5000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124472917057 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨42, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (4131403255909 / 5000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124472917057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_43 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (16518822927747 / 20000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (56223746043 / 2500000000000 : ℝ))
      (E := (cell12722 ⟨43, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (16518822927747 / 20000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (56223746043 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_44 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (20640046925907 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449790774691 / 20000000000000 : ℝ))
      (E := (cell12722 ⟨44, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (20640046925907 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449790774691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_45 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41263142141741 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248957869201 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨45, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41263142141741 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248957869201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_46 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (20623101087267 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248961886311 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨46, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (20623101087267 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248961886311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_47 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (10307318483913 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124482932093 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨47, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (10307318483913 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124482932093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_48 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (10303089352657 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248969918733 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨48, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (10303089352657 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248969918733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_49 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (20597726292533 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248973871027 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨49, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (20597726292533 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248973871027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_50 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82357118889287 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449795579111 / 20000000000000 : ℝ))
      (E := (cell12722 ⟨50, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82357118889287 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449795579111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_51 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41161677975109 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248981930843 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨51, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41161677975109 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248981930843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_52 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (16457923264913 / 20000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (224898591511 / 10000000000000 : ℝ))
      (E := (cell12722 ⟨52, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (16457923264913 / 20000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (224898591511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_53 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82255899984111 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (112449495219 / 5000000000000 : ℝ))
      (E := (cell12722 ⟨53, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82255899984111 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (112449495219 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_54 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41111103450389 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248993954563 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨54, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41111103450389 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248993954563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_55 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (8218853704663 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124498972073 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨55, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (8218853704663 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124498972073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_56 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (8215489039387 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562250482149 / 25000000000000 : ℝ))
      (E := (cell12722 ⟨56, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (8215489039387 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562250482149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_57 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82121266914839 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562251490817 / 25000000000000 : ℝ))
      (E := (cell12722 ⟨57, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82121266914839 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562251490817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_58 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82087666582017 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562252481471 / 25000000000000 : ℝ))
      (E := (cell12722 ⟨58, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82087666582017 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562252481471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_59 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82054089368019 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2249013930559 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨59, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82054089368019 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2249013930559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12723_40 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41348017088761 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248815893003 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨40, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41348017088761 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248815893003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_41 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82662036822531 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248819904067 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨41, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82662036822531 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248819904067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_42 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (4131403153533 / 5000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449764776611 / 20000000000000 : ℝ))
      (E := (cell12723 ⟨42, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (4131403153533 / 5000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449764776611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_43 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (20648528223059 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (22488278879 / 1000000000000 : ℝ))
      (E := (cell12723 ⟨43, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (20648528223059 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (22488278879 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_44 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41280093128867 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449766383513 / 20000000000000 : ℝ))
      (E := (cell12723 ⟨44, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41280093128867 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449766383513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_45 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82526283137779 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248835911931 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨45, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82526283137779 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248835911931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_46 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41246201751571 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248839928351 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨46, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41246201751571 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248839928351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_47 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (10307318415593 / 12500000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (140552744139 / 6250000000000 : ℝ))
      (E := (cell12723 ⟨47, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (10307318415593 / 12500000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (140552744139 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_48 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82424714573649 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (56221197563 / 2500000000000 : ℝ))
      (E := (cell12723 ⟨48, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82424714573649 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (56221197563 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_49 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82390905221067 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (17990815321 / 800000000000 : ℝ))
      (E := (cell12723 ⟨49, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82390905221067 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (17990815321 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_50 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82357119238353 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449771188343 / 20000000000000 : ℝ))
      (E := (cell12723 ⟨50, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82357119238353 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449771188343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_51 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (16464671319401 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124429960371 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨51, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (16464671319401 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124429960371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_52 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (16457923453733 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248863967449 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨52, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (16457923453733 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248863967449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_53 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (16451180245023 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248867960837 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨53, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (16451180245023 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248867960837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_54 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82222208438279 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124435978371 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨54, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82222208438279 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124435978371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_55 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (4109426944011 / 5000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124437975893 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨55, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (4109426944011 / 5000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124437975893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_56 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82154892523143 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124440000753 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨56, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82154892523143 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124440000753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_57 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (8212126933939 / 10000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124441991939 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨57, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (8212126933939 / 10000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124441991939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_58 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82087669301441 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (89955520527 / 4000000000000 : ℝ))
      (E := (cell12723 ⟨58, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82087669301441 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (89955520527 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_59 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (10256761547739 / 12500000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449778393373 / 20000000000000 : ℝ))
      (E := (cell12723 ⟨59, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (10256761547739 / 12500000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449778393373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12724_40 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82696031527581 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248693946391 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨40, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82696031527581 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248693946391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_41 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (16532406894881 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562174488337 / 25000000000000 : ℝ))
      (E := (cell12724 ⟨41, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (16532406894881 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562174488337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_42 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41314030511967 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248701987717 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨42, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41314030511967 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248701987717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_43 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41297055573247 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (112435299493 / 5000000000000 : ℝ))
      (E := (cell12724 ⟨43, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41297055573247 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (112435299493 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_44 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82560184812561 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (140544372417 / 6250000000000 : ℝ))
      (E := (cell12724 ⟨44, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82560184812561 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (140544372417 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_45 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (2063157049819 / 2500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562178502641 / 25000000000000 : ℝ))
      (E := (cell12724 ⟨45, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (2063157049819 / 2500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562178502641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_46 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (16498480531573 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248717967463 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨46, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (16498480531573 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248717967463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_47 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (20614636694699 / 25000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449744400857 / 20000000000000 : ℝ))
      (E := (cell12724 ⟨47, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (20614636694699 / 25000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449744400857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_48 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41212357163309 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (140545375083 / 6250000000000 : ℝ))
      (E := (cell12724 ⟨48, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41212357163309 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (140545375083 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_49 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82390905272541 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248730015369 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨49, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82390905272541 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248730015369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_50 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82357119587923 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124366992547 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨50, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82357119587923 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124366992547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_51 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82323357244261 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248738025913 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨51, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82323357244261 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248738025913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_52 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82289618213197 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124371008541 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨52, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82289618213197 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124371008541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_53 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (16451180493303 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248746014623 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨53, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (16451180493303 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248746014623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_54 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (4111110498807 / 5000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124375007683 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨54, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (4111110498807 / 5000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124375007683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_55 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (16437708142827 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562188503983 / 25000000000000 : ℝ))
      (E := (cell12724 ⟨55, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (16437708142827 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562188503983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_56 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41077447326353 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (140547379491 / 6250000000000 : ℝ))
      (E := (cell12724 ⟨56, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41077447326353 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (140547379491 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_57 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (16424254352839 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124381030557 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨57, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (16424254352839 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124381030557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_58 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41043836010541 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124383019403 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨58, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41043836010541 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124383019403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_59 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41027047697993 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248770059917 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨59, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41027047697993 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248770059917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

end BstLean.Part268
