import BstLean.Part268CellShard25Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12975_40 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82695346401877 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219027733953 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨40, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82695346401877 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219027733953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_41 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41330711416929 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219031757913 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨41, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41330711416929 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219031757913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_42 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (16525504553457 / 20000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443807148653 / 20000000000000 : ℝ))
      (E := (cell12975 ⟨42, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (16525504553457 / 20000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443807148653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_43 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82593646172669 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (88761589903 / 4000000000000 : ℝ))
      (E := (cell12975 ⟨43, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82593646172669 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (88761589903 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_44 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82559793020669 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219043769423 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨44, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82559793020669 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219043769423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_45 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82525963282091 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219047748281 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨45, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82525963282091 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219047748281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_46 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (5155759807993 / 6250000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219051800053 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨46, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (5155759807993 / 6250000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219051800053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_47 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82458373929161 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109527902433 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨47, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82458373929161 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109527902433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_48 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82424614257151 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554764954833 / 25000000000000 : ℝ))
      (E := (cell12975 ⟨48, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82424614257151 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554764954833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_49 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82390877883247 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554765960239 / 25000000000000 : ℝ))
      (E := (cell12975 ⟨49, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82390877883247 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554765960239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_50 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (4117858238949 / 5000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (88762712321 / 4000000000000 : ℝ))
      (E := (cell12975 ⟨50, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (4117858238949 / 5000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (88762712321 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_51 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82323474916023 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443814367123 / 20000000000000 : ℝ))
      (E := (cell12975 ⟨51, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82323474916023 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443814367123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_52 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82289808266191 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219075861613 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨52, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82289808266191 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219075861613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_53 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82256164801439 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219079823607 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨53, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82256164801439 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219079823607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_54 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41111272246931 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109541918091 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨54, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41111272246931 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109541918091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_55 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (16437789463139 / 20000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277385986957 / 12500000000000 : ℝ))
      (E := (cell12975 ⟨55, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (16437789463139 / 20000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277385986957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_56 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82155373239311 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (13869324249 / 625000000000 : ℝ))
      (E := (cell12975 ⟨56, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82155373239311 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (13869324249 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_57 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (4106091111861 / 5000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (55477397571 / 2500000000000 : ℝ))
      (E := (cell12975 ⟨57, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (4106091111861 / 5000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (55477397571 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_58 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (20522073570517 / 25000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219099901159 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨58, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (20522073570517 / 25000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219099901159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_59 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82054789346639 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219103929437 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨59, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82054789346639 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219103929437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12976_40 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (82695332162053 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218912881077 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨40, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (82695332162053 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218912881077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_41 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (330645634401 / 400000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218916901191 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨41, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (330645634401 / 400000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218916901191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_42 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (5164219283743 / 6250000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109460441371 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨42, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (5164219283743 / 6250000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109460441371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_43 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41296815975739 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109462471071 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨43, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41296815975739 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109462471071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_44 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41279889402839 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218928901439 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨44, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41279889402839 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218928901439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_45 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (5157871817081 / 6250000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (88757317421 / 4000000000000 : ℝ))
      (E := (cell12976 ⟨45, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (5157871817081 / 6250000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (88757317421 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_46 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (20623035681321 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (221893692479 / 10000000000000 : ℝ))
      (E := (cell12976 ⟨46, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (20623035681321 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (221893692479 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_47 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41229179866371 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109470463017 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨47, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41229179866371 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109470463017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_48 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (82424600066913 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (88757797479 / 4000000000000 : ℝ))
      (E := (cell12976 ⟨48, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (82424600066913 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (88757797479 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_49 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (16478172739837 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218948955121 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨49, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (16478172739837 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218948955121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_50 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (643415239071 / 781250000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109476488883 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨50, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (643415239071 / 781250000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109476488883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_51 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (82323460744297 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218957001993 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨51, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (82323460744297 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218957001993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_52 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (131663670561 / 160000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (88758440987 / 4000000000000 : ℝ))
      (E := (cell12976 ⟨52, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (131663670561 / 160000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (88758440987 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_53 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (82256150642029 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554741260619 / 25000000000000 : ℝ))
      (E := (cell12976 ⟨53, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (82256150642029 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554741260619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_54 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (82222530340603 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (44379381037 / 2000000000000 : ℝ))
      (E := (cell12976 ⟨54, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (82222530340603 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (44379381037 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_55 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (82188933168583 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109486524521 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨55, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (82188933168583 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109486524521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_56 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (4107767954917 / 5000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218977030093 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨56, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (4107767954917 / 5000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218977030093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_57 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (16424361620477 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109490525003 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨57, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (16424361620477 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109490525003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_58 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (20522070038341 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554746261321 / 25000000000000 : ℝ))
      (E := (cell12976 ⟨58, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (20522070038341 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554746261321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_59 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41027387612031 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109494535283 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨59, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41027387612031 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109494535283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12977_40 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82695317924427 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109399041301 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨40, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82695317924427 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109399041301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_41 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82661394368839 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109401049447 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨41, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82661394368839 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109401049447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_42 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82627494314687 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218806076669 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨42, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82627494314687 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218806076669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_43 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82593617732481 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (110940506617 / 5000000000000 : ℝ))
      (E := (cell12977 ⟨43, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82593617732481 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (110940506617 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_44 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82559764592881 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218814087953 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨44, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82559764592881 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218814087953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_45 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82525934866693 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109409059201 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨45, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82525934866693 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109409059201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_46 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82492128524871 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (88752884163 / 4000000000000 : ℝ))
      (E := (cell12977 ⟨46, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82492128524871 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (88752884163 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_47 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (41229172769257 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (221882616071 / 10000000000000 : ℝ))
      (E := (cell12977 ⟨47, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (41229172769257 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (221882616071 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_48 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (5151536617429 / 6250000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (138676885511 / 6250000000000 : ℝ))
      (E := (cell12977 ⟨48, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (5151536617429 / 6250000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (138676885511 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_49 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82390849517311 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218834182891 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨49, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82390849517311 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218834182891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_50 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (10294642053173 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (277354767893 / 12500000000000 : ℝ))
      (E := (cell12977 ⟨50, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (10294642053173 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (277354767893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_51 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (41161723287379 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218842164009 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨51, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (41161723287379 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218842164009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_52 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (41144889968623 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (17750769467 / 800000000000 : ℝ))
      (E := (cell12977 ⟨52, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (41144889968623 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (17750769467 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_53 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (16451227296961 / 20000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109425098953 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨53, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (16451227296961 / 20000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109425098953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_54 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82222516189529 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443770840811 / 20000000000000 : ℝ))
      (E := (cell12977 ⟨54, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82222516189529 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443770840811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_55 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82188919023653 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (221885819807 / 10000000000000 : ℝ))
      (E := (cell12977 ⟨55, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82188919023653 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (221885819807 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_56 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82155344959551 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218862235137 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨56, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82155344959551 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218862235137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_57 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82121793969731 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554716562997 / 25000000000000 : ℝ))
      (E := (cell12977 ⟨57, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82121793969731 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554716562997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_58 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82088266026841 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (277358780531 / 12500000000000 : ℝ))
      (E := (cell12977 ⟨58, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82088266026841 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (277358780531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_59 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (5128422568979 / 6250000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218874266559 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨59, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (5128422568979 / 6250000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218874266559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12978_40 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (82695303688997 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109341639879 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨40, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (82695303688997 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109341639879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_41 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (82661380139623 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218687292229 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨41, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (82661380139623 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218687292229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_42 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (516421750573 / 625000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218691325049 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨42, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (516421750573 / 625000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218691325049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_43 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41296801757839 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (221869531817 / 10000000000000 : ℝ))
      (E := (cell12978 ⟨43, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41296801757839 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (221869531817 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_44 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (82559750382277 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218699328967 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨44, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (82559750382277 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218699328967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_45 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (82525920662283 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218703355803 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨45, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (82525920662283 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218703355803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_46 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (1649842286533 / 2000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (554676834477 / 25000000000000 : ℝ))
      (E := (cell12978 ⟨46, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (1649842286533 / 2000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (554676834477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_47 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (20614582836619 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443742266417 / 20000000000000 : ℝ))
      (E := (cell12978 ⟨47, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (20614582836619 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443742266417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_48 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (16484914338601 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (554678834013 / 25000000000000 : ℝ))
      (E := (cell12978 ⟨48, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (16484914338601 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (554678834013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_49 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (659126682701 / 800000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443743869463 / 20000000000000 : ℝ))
      (E := (cell12978 ⟨49, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (659126682701 / 800000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443743869463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_50 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (20589280562967 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (69335105099 / 3125000000000 : ℝ))
      (E := (cell12978 ⟨50, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (20589280562967 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (69335105099 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_51 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (16464686481481 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (277340922587 / 12500000000000 : ℝ))
      (E := (cell12978 ⟨51, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (16464686481481 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (277340922587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_52 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (20572441444013 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218731396771 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨52, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (20572441444013 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218731396771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_53 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (16451224465953 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (277341926007 / 12500000000000 : ℝ))
      (E := (cell12978 ⟨53, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (16451224465953 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (277341926007 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_54 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41111251020319 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109369705503 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨54, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41111251020319 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109369705503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_55 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41094452440453 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (17333933289 / 781250000000 : ℝ))
      (E := (cell12978 ⟨55, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41094452440453 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (17333933289 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_56 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (82155330822943 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109373717913 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨56, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (82155330822943 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109373717913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_57 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41060889919629 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109375724807 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨57, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41060889919629 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109375724807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_58 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41044125951249 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109377719429 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨58, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41044125951249 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109377719429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_59 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41027373492723 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109379729099 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨59, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41027373492723 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109379729099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12979_40 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (20673822363941 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109284265659 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨40, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (20673822363941 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109284265659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_41 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82661365912603 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277321567499 / 12500000000000 : ℝ))
      (E := (cell12979 ⟨41, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82661365912603 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277321567499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_42 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (20656866467717 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109288255121 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨42, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (20656866467717 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109288255121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_43 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82593589301069 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218580558479 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨43, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82593589301069 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218580558479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_44 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (41279868086933 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218584565617 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨44, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (41279868086933 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218584565617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_45 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (2578934576877 / 3125000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (55464714721 / 2500000000000 : ℝ))
      (E := (cell12979 ⟨45, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (2578934576877 / 3125000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (55464714721 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_46 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82492100130619 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218592567379 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨46, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82492100130619 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218592567379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_47 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (20614579289157 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554649139509 / 25000000000000 : ℝ))
      (E := (cell12979 ⟨47, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (20614579289157 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554649139509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_48 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (16484911501867 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218600617489 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨48, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (16484911501867 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218600617489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_49 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (1287356580627 / 1562500000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218604625347 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨49, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (1287356580627 / 1562500000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218604625347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_50 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (41178554040269 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218608637841 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨50, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (41178554040269 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218608637841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_51 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (41161709121119 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277326581507 / 12500000000000 : ℝ))
      (E := (cell12979 ⟨51, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (41161709121119 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277326581507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_52 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82289751617043 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218616605809 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨52, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82289751617043 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218616605809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_53 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (20564027044227 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (69331896029 / 3125000000000 : ℝ))
      (E := (cell12979 ⟨53, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (20564027044227 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (69331896029 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_54 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (8222248789393 / 10000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109312336351 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨54, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (8222248789393 / 10000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109312336351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_55 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (41094445370171 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218628660433 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨55, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (41094445370171 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218628660433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_56 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82155316688517 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554658172827 / 25000000000000 : ℝ))
      (E := (cell12979 ⟨56, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82155316688517 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554658172827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_57 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (16424353142193 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218636702059 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨57, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (16424353142193 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218636702059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_58 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82088237780333 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277330086039 / 12500000000000 : ℝ))
      (E := (cell12979 ⟨58, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82088237780333 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277330086039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_59 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (16410946573881 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (443728940941 / 20000000000000 : ℝ))
      (E := (cell12979 ⟨59, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (16410946573881 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (443728940941 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12980_40 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82695275224727 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (221845377851 / 10000000000000 : ℝ))
      (E := (cell12980 ⟨40, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82695275224727 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (221845377851 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_41 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41330675843889 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218457783389 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨41, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41330675843889 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218457783389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_42 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (330509806609 / 400000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218461808709 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨42, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (330509806609 / 400000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218461808709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_43 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82593575088653 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109232897211 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨43, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82593575088653 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109232897211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_44 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41279860983823 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218469797903 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨44, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41279860983823 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218469797903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_45 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82525892260037 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109236908757 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨45, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82525892260037 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109236908757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_46 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41246042968389 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109238925701 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨46, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41246042968389 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109238925701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_47 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82458302968969 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109240919281 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨47, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82458302968969 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109240919281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_48 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82424543327853 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554621458901 / 25000000000000 : ℝ))
      (E := (cell12980 ⟨48, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82424543327853 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554621458901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_49 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82390806984817 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443697968007 / 20000000000000 : ℝ))
      (E := (cell12980 ⟨49, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82390806984817 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443697968007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_50 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41178546955697 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554623462287 / 25000000000000 : ℝ))
      (E := (cell12980 ⟨50, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41178546955697 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554623462287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_51 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (10290425509907 / 12500000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218497860027 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨51, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (10290425509907 / 12500000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218497860027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_52 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41144868730109 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (277312733693 / 12500000000000 : ℝ))
      (E := (cell12980 ⟨52, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41144868730109 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (277312733693 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_53 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (20564023506559 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554626468591 / 25000000000000 : ℝ))
      (E := (cell12980 ⟨53, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (20564023506559 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554626468591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_54 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (20555618437351 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218509930043 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨54, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (20555618437351 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218509930043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_55 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41094438300979 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443702782929 / 20000000000000 : ℝ))
      (E := (cell12980 ⟨55, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41094438300979 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443702782929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_56 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82155302556271 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109258971219 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨56, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82155302556271 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109258971219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_57 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (20530437896213 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218521950151 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨57, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (20530437896213 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218521950151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_58 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (20522055915087 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218525933413 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨58, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (20522055915087 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218525933413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_59 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82054718755543 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218529946861 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨59, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82054718755543 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218529946861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12981_40 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (16539052199177 / 20000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (221833908011 / 10000000000000 : ℝ))
      (E := (cell12981 ⟨40, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (16539052199177 / 20000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (221833908011 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_41 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82661337465147 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218343081217 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨41, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82661337465147 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218343081217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_42 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (3305097497433 / 4000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218347102811 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨42, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (3305097497433 / 4000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218347102811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_43 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82593560878429 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554587771211 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨43, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82593560878429 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554587771211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_44 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41279853881809 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218355084693 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨44, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41279853881809 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218355084693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_45 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (412629390311 / 500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554589775179 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨45, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (412629390311 / 500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554589775179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_46 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82492071745127 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218363131063 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨46, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82492071745127 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218363131063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_47 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41229144391749 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (277295889341 / 12500000000000 : ℝ))
      (E := (cell12981 ⟨47, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41229144391749 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (277295889341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_48 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41212264574279 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218371108321 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨48, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41212264574279 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218371108321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_49 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41195396405847 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554593792083 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨49, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41195396405847 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554593792083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_50 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (20589269936109 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (69324349191 / 3125000000000 : ℝ))
      (E := (cell12981 ⟨50, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (20589269936109 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (69324349191 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_51 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82323389918459 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218383181703 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨51, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82323389918459 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218383181703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_52 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82289723305577 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218387187979 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨52, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82289723305577 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218387187979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_53 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41128039938873 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109195594801 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨53, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41128039938873 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109195594801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_54 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82222459607061 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554598795757 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨54, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82222459607061 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554598795757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_55 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (20547215616439 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218399223629 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨55, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (20547215616439 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218399223629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_56 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (16431057685241 / 20000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109201594607 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨56, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (16431057685241 / 20000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109201594607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_57 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41060868730459 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (277300906633 / 12500000000000 : ℝ))
      (E := (cell12981 ⟨57, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41060868730459 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (277300906633 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_58 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82088209542541 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109205616679 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨58, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82088209542541 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109205616679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_59 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82054704643857 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109207621943 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨59, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82054704643857 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109207621943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12982_40 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41347623384619 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218224377343 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨40, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41347623384619 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218224377343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_41 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82661323244711 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109114187339 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨41, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82661323244711 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109114187339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_42 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82627423221593 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218232392549 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨42, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82627423221593 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218232392549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_43 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82593546670397 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277279546363 / 12500000000000 : ℝ))
      (E := (cell12982 ⟨43, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82593546670397 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277279546363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_44 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41279846780891 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109120212993 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨44, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41279846780891 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109120212993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_45 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82525863866553 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (138640277403 / 6250000000000 : ℝ))
      (E := (cell12982 ⟨45, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82525863866553 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (138640277403 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_46 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (16498411511133 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218248406363 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨46, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (16498411511133 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218248406363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_47 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (10307284325027 / 12500000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (69320388921 / 3125000000000 : ℝ))
      (E := (cell12982 ⟨47, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (10307284325027 / 12500000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (69320388921 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_48 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82424514971451 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218256435639 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨48, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82424514971451 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218256435639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_49 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (20597694660189 / 25000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277282554161 / 12500000000000 : ℝ))
      (E := (cell12982 ⟨49, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (20597694660189 / 25000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277282554161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_50 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (5147316598729 / 6250000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (221826443571 / 10000000000000 : ℝ))
      (E := (cell12982 ⟨50, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (5147316598729 / 6250000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (221826443571 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_51 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82323375759847 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218268439991 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨51, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82323375759847 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218268439991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_52 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (514310682207 / 625000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218272502057 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨52, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (514310682207 / 625000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218272502057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_53 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82256065731439 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109138250243 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨53, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82256065731439 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109138250243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_54 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82222445466899 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218280490763 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨54, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82222445466899 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218280490763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_55 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (16437769666347 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218284528259 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨55, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (16437769666347 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218284528259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_56 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82155274298319 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218288549937 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨56, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82155274298319 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218288549937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_57 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41060861669581 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109146275813 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨57, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41060861669581 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109146275813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_58 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82088195426911 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443659305791 / 20000000000000 : ℝ))
      (E := (cell12982 ⟨58, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82088195426911 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443659305791 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_59 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82054690534349 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109150268281 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨59, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82054690534349 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109150268281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12983_40 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41347616272393 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554527417553 / 25000000000000 : ℝ))
      (E := (cell12983 ⟨40, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41347616272393 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554527417553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_41 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (82661309026467 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (138632107661 / 6250000000000 : ℝ))
      (E := (cell12983 ⟨41, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (82661309026467 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (138632107661 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_42 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41313704504777 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109058868373 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨42, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41313704504777 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109058868373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_43 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (82593532464557 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109060855723 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨43, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (82593532464557 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109060855723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_44 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (16511935872427 / 20000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109062852027 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨44, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (16511935872427 / 20000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109062852027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_45 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (10315731209137 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218129712929 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨45, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (10315731209137 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218129712929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_46 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (10311505421049 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218133736219 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨46, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (10311505421049 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218133736219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_47 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41229130209561 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109068885929 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨47, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41229130209561 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109068885929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_48 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (8242450079653 / 10000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109070879301 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨48, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (8242450079653 / 10000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109070879301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_49 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (16478152894401 / 20000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218145752871 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨49, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (16478152894401 / 20000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218145752871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_50 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (20589262854269 / 25000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218149810971 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨50, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (20589262854269 / 25000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218149810971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_51 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41161680801709 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218153811989 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨51, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41161680801709 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218153811989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_52 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41144847501423 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218157811783 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨52, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41144847501423 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218157811783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_53 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41128025793657 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218161807017 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨53, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41128025793657 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218161807017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_54 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41111215664459 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (34658841457 / 1562500000000 : ℝ))
      (E := (cell12983 ⟨54, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41111215664459 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (34658841457 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_55 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (82188834199893 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (110908491427 / 5000000000000 : ℝ))
      (E := (cell12983 ⟨55, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (82188834199893 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (110908491427 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_56 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (20538815043153 / 25000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218173847161 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨56, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (20538815043153 / 25000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218173847161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_57 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (16424341843917 / 20000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218177845839 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨57, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (16424341843917 / 20000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218177845839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_58 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (82088181313459 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109090939699 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨58, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (82088181313459 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109090939699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_59 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (10256834553377 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218185884111 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨59, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (10256834553377 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218185884111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12984_40 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82695218322527 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554498754373 / 25000000000000 : ℝ))
      (E := (cell12984 ⟨40, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82695218322527 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554498754373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_41 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82661294810417 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (221799906611 / 10000000000000 : ℝ))
      (E := (cell12984 ⟨41, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82661294810417 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (221799906611 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_42 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82627394799707 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (110900153829 / 5000000000000 : ℝ))
      (E := (cell12984 ⟨42, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82627394799707 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (110900153829 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_43 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (20648379565227 / 25000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554501761907 / 25000000000000 : ℝ))
      (E := (cell12984 ⟨43, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (20648379565227 / 25000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554501761907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_44 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82559665164679 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277251386937 / 12500000000000 : ℝ))
      (E := (cell12984 ⟨44, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82559665164679 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277251386937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_45 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82525835481827 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1109007550417 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨45, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82525835481827 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1109007550417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_46 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (41246014591653 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277252390079 / 12500000000000 : ℝ))
      (E := (cell12984 ⟨46, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (41246014591653 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277252390079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_47 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (41229123120107 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218023093887 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨47, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (41229123120107 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218023093887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_48 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (20606121655949 / 25000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218027136169 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨48, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (20606121655949 / 25000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218027136169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_49 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (41195375152719 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1109015563543 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨49, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (41195375152719 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1109015563543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_50 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82357037256673 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554508780717 / 25000000000000 : ℝ))
      (E := (cell12984 ⟨50, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82357037256673 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554508780717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_51 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82323347449173 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218039179633 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨51, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82323347449173 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218039179633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_52 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (41144840427377 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218043176211 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨52, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (41144840427377 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218043176211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_53 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (8225603744537 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (88721886731 / 4000000000000 : ℝ))
      (E := (cell12984 ⟨53, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (8225603744537 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (88721886731 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_54 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (41111208596559 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1109025605691 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨54, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (41111208596559 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1109025605691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_55 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82188820070231 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554513795899 / 25000000000000 : ℝ))
      (E := (cell12984 ⟨55, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82188820070231 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554513795899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_56 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (20538811512271 / 25000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (138628699949 / 6250000000000 : ℝ))
      (E := (cell12984 ⟨56, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (20538811512271 / 25000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (138628699949 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_57 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (16424339020437 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218063194877 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨57, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (16424339020437 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2218063194877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_58 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82088167202183 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (443613445099 / 20000000000000 : ℝ))
      (E := (cell12984 ⟨58, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82088167202183 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (443613445099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_59 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (4102733116093 / 5000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (138629451707 / 6250000000000 : ℝ))
      (E := (cell12984 ⟨59, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (4102733116093 / 5000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (138629451707 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12985_40 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41347602051231 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108940209591 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨40, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41347602051231 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108940209591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_41 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82661280596559 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108942202641 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨41, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82661280596559 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108942202641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_42 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82627380592051 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108944206027 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨42, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82627380592051 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108944206027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_43 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82593504059449 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108946219147 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨43, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82593504059449 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108946219147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_44 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (20639912742353 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217896482579 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨44, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (20639912742353 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217896482579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_45 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (20631455323187 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217900484379 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨45, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (20631455323187 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217900484379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_46 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82492015000409 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217904500687 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨46, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82492015000409 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217904500687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_47 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41229116031747 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217908470497 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨47, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41229116031747 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217908470497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_48 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82424472453247 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217912509381 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨48, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82424472453247 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217912509381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_49 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82390736141057 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (138619781059 / 6250000000000 : ℝ))
      (E := (cell12985 ⟨49, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82390736141057 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (138619781059 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_50 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41178511549227 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217920489419 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨50, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41178511549227 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217920489419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_51 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82323333297111 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217924542923 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨51, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82323333297111 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217924542923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_52 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (20572416677211 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108964268143 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨52, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (20572416677211 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108964268143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_53 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82256023305607 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108966262591 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨53, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82256023305607 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108966262591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_54 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82222403059497 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108968282583 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨54, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82222403059497 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108968282583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_55 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82188805942749 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (554485148357 / 25000000000000 : ℝ))
      (E := (cell12985 ⟨55, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82188805942749 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (554485148357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_56 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41077615963867 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (277243075751 / 12500000000000 : ℝ))
      (E := (cell12985 ⟨56, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41077615963867 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (277243075751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_57 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82121680986963 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108974299369 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨57, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82121680986963 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108974299369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_58 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (20522038273271 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217952626441 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨58, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (20522038273271 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217952626441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_59 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82054648218879 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217956625387 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨59, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82054648218879 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217956625387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12986_40 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (82695189884589 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217765816513 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨40, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (82695189884589 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217765816513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_41 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (20665316596223 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (221776985769 / 10000000000000 : ℝ))
      (E := (cell12986 ⟨41, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (20665316596223 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (221776985769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_42 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (41313683193293 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217773860811 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨42, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (41313683193293 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217773860811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_43 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (4129674493009 / 5000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217777824601 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨43, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (4129674493009 / 5000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217777824601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_44 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16511927355267 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277222733163 / 12500000000000 : ℝ))
      (E := (cell12986 ⟨44, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16511927355267 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277222733163 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_45 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (1289465736029 / 1562500000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217785863569 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨45, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (1289465736029 / 1562500000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217785863569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_46 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (41246000409849 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217789876387 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨46, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (41246000409849 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217789876387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_47 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (82458217888959 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217793901691 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨47, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (82458217888959 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217793901691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_48 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (20606114571221 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108898939119 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨48, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (20606114571221 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108898939119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_49 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (4119536098943 / 5000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108900960717 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨49, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (4119536098943 / 5000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108900960717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_50 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (82357008942417 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (554451477657 / 25000000000000 : ℝ))
      (E := (cell12986 ⟨50, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (82357008942417 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (554451477657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_51 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (82323319147231 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217809901863 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨51, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (82323319147231 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217809901863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_52 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16457930513023 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217813951067 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨52, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16457930513023 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217813951067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_53 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (3290240366721 / 4000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108908968409 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨53, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (3290240366721 / 4000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108908968409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_54 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (82222388928057 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108910986851 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨54, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (82222388928057 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108910986851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_55 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (20547197954361 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217825998913 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨55, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (20547197954361 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217825998913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_56 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (82155217808561 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443566001697 / 20000000000000 : ℝ))
      (E := (cell12986 ⟨56, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (82155217808561 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443566001697 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_57 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (82121666873917 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108916999127 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨57, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (82121666873917 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108916999127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_58 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (1026101737327 / 1250000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217838023041 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨58, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (1026101737327 / 1250000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217838023041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_59 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (10256829264759 / 12500000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217842019119 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨59, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (10256829264759 / 12500000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217842019119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12987_40 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (82695175668909 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (69301602133 / 3125000000000 : ℝ))
      (E := (cell12987 ⟨40, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (82695175668909 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (69301602133 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_41 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41330626087709 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217655246939 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨41, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41330626087709 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217655246939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_42 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (82627352183311 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554414811597 / 25000000000000 : ℝ))
      (E := (cell12987 ⟨42, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (82627352183311 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554414811597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_43 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (82593475663101 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443532653079 / 20000000000000 : ℝ))
      (E := (cell12987 ⟨43, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (82593475663101 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443532653079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_44 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (16511924517089 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (110883365127 / 5000000000000 : ℝ))
      (E := (cell12987 ⟨44, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (16511924517089 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (110883365127 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_45 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (1289465514393 / 1562500000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217671297293 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨45, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (1289465514393 / 1562500000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217671297293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_46 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41245993320587 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108837653323 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨46, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41245993320587 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108837653323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_47 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (8245820371661 / 10000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (221767932853 / 10000000000000 : ℝ))
      (E := (cell12987 ⟨47, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (8245820371661 / 10000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (221767932853 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_48 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (16484888823741 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (277210412713 / 12500000000000 : ℝ))
      (E := (cell12987 ⟨48, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (16484888823741 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (277210412713 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_49 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41195353909423 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554421835393 / 25000000000000 : ℝ))
      (E := (cell12987 ⟨49, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41195353909423 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554421835393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_50 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (20589248697141 / 25000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554422831871 / 25000000000000 : ℝ))
      (E := (cell12987 ⟨50, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (20589248697141 / 25000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554422831871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_51 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (82323304999533 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443539074903 / 20000000000000 : ℝ))
      (E := (cell12987 ⟨51, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (82323304999533 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443539074903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_52 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (82289638423567 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108849680749 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨52, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (82289638423567 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108849680749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_53 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41127997516311 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (138606462699 / 6250000000000 : ℝ))
      (E := (cell12987 ⟨53, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41127997516311 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (138606462699 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_54 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (16444474959759 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217707377891 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨54, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (16444474959759 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217707377891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_55 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41094388847159 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217711400049 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨55, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41094388847159 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217711400049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_56 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41077601845783 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (277214425827 / 12500000000000 : ℝ))
      (E := (cell12987 ⟨56, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41077601845783 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (277214425827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_57 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (10265206595381 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (138607462089 / 6250000000000 : ℝ))
      (E := (cell12987 ⟨57, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (10265206595381 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (138607462089 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_58 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (20522031220353 / 25000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217723415297 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨58, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (20522031220353 / 25000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217723415297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_59 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (1025682750243 / 1250000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (88709098709 / 4000000000000 : ℝ))
      (E := (cell12987 ⟨59, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (1025682750243 / 1250000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (88709098709 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12988_40 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (4134758072771 / 5000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217536715641 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨40, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (4134758072771 / 5000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217536715641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_41 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41330618984067 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554385172657 / 25000000000000 : ℝ))
      (E := (cell12988 ⟨41, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41330618984067 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554385172657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_42 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (82627337982227 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217544686427 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨42, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (82627337982227 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217544686427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_43 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (8259346146821 / 10000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217548701833 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨43, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (8259346146821 / 10000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217548701833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_44 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (10319951049593 / 12500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217552735421 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨44, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (10319951049593 / 12500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217552735421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_45 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (16505155747727 / 20000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217556726663 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨45, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (16505155747727 / 20000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217556726663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_46 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (20622993116209 / 25000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217560732551 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨46, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (20622993116209 / 25000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217560732551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_47 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (82458189546447 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (277195593877 / 12500000000000 : ℝ))
      (E := (cell12988 ⟨47, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (82458189546447 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (277195593877 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_48 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (82424429954711 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217568779779 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨48, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (82424429954711 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217568779779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_49 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (10298836707627 / 12500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217572757359 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨49, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (10298836707627 / 12500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217572757359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_50 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (82356980636893 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217576798999 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨50, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (82356980636893 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217576798999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_51 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (643150709797 / 781250000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217580783787 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨51, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (643150709797 / 781250000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217580783787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_52 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (411448121421 / 500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554396206659 / 25000000000000 : ℝ))
      (E := (cell12988 ⟨52, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (411448121421 / 500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554396206659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_53 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (411279904497 / 500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217588806123 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨53, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (411279904497 / 500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217588806123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_54 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (82222360671711 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217592836837 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨54, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (82222360671711 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217592836837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_55 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (82188763573369 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217596855967 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨55, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (82188763573369 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217596855967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_56 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (82155189576747 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217600859551 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨56, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (82155189576747 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217600859551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_57 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41060819327177 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217604843423 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨57, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41060819327177 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217604843423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_58 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41044055389419 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1108804431203 / 50000000000000 : ℝ))
      (E := (cell12988 ⟨58, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41044055389419 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1108804431203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_59 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41027302961491 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (221761291199 / 10000000000000 : ℝ))
      (E := (cell12988 ⟨59, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41027302961491 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (221761291199 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12989_40 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (82695147244123 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554355539667 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨40, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (82695147244123 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554355539667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_41 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (516632648519 / 625000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217426188759 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨41, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (516632648519 / 625000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217426188759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_42 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (82627323783331 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108715090467 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨42, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (82627323783331 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108715090467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_43 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (20648361818877 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (55435854819 / 2500000000000 : ℝ))
      (E := (cell12989 ⟨43, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (20648361818877 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (55435854819 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_44 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (82559594210231 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443487644563 / 20000000000000 : ℝ))
      (E := (cell12989 ⟨44, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (82559594210231 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443487644563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_45 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (16505152911661 / 20000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217442210571 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨45, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (16505152911661 / 20000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217442210571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_46 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (20622989572671 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217446213019 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨46, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (20622989572671 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217446213019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_47 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (20614543844617 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (221745022809 / 10000000000000 : ℝ))
      (E := (cell12989 ⟨47, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (20614543844617 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (221745022809 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_48 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (824244157929 / 1000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (34647722711 / 1562500000000 : ℝ))
      (E := (cell12989 ⟨48, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (824244157929 / 1000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (34647722711 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_49 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (10298834938171 / 12500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108729113891 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨49, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (10298834938171 / 12500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108729113891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_50 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (20589241621851 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443492453233 / 20000000000000 : ℝ))
      (E := (cell12989 ⟨50, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (20589241621851 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443492453233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_51 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (2058081917767 / 2500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108733123871 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨51, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (2058081917767 / 2500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108733123871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_52 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (20572402536753 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554367571857 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨52, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (20572402536753 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554367571857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_53 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (16451193353671 / 20000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554368580719 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨53, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (16451193353671 / 20000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554368580719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_54 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41111173273403 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554369572859 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨54, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41111173273403 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554369572859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_55 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41094374727299 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217482307539 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨55, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41094374727299 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217482307539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_56 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (10269396933013 / 12500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217486308143 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨56, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (10269396933013 / 12500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217486308143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_57 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (16424324909567 / 20000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108745174127 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨57, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (16424324909567 / 20000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108745174127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_58 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41044048339219 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (221749436437 / 10000000000000 : ℝ))
      (E := (cell12989 ⟨58, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41044048339219 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (221749436437 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_59 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (82054591828697 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108749175957 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨59, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (82054591828697 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108749175957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12990_40 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82695133035017 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217307656111 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨40, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82695133035017 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217307656111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_41 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (10332651195017 / 12500000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217311682533 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨41, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (10332651195017 / 12500000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217311682533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_42 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (661018476693 / 800000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217315671083 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨42, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (661018476693 / 800000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217315671083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_43 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (41296716542497 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (554329919833 / 25000000000000 : ℝ))
      (E := (cell12990 ⟨43, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (41296716542497 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (554329919833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_44 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (5159973751619 / 6250000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (4330710363 / 195312500000 : ℝ))
      (E := (cell12990 ⟨44, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (5159973751619 / 6250000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (4330710363 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_45 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (128946484969 / 156250000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217327690127 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨45, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (128946484969 / 156250000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217327690127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_46 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82491944118717 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108665844567 / 50000000000000 : ℝ))
      (E := (cell12990 ⟨46, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82491944118717 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108665844567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_47 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82458161212673 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (554333925203 / 25000000000000 : ℝ))
      (E := (cell12990 ⟨47, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82458161212673 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (554333925203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_48 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (10303050204159 / 12500000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217339722879 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨48, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (10303050204159 / 12500000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217339722879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_49 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82390665351903 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (55433593821 / 2500000000000 : ℝ))
      (E := (cell12990 ⟨49, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82390665351903 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (55433593821 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_50 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (16471390468019 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277168473499 / 12500000000000 : ℝ))
      (E := (cell12990 ⟨50, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (16471390468019 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277168473499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_51 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (20580815642381 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217351766383 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨51, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (20580815642381 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217351766383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_52 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (20572399003001 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (138584737683 / 6250000000000 : ℝ))
      (E := (cell12990 ⟨52, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (20572399003001 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (138584737683 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_53 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (8225595263949 / 10000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217359776201 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨53, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (8225595263949 / 10000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217359776201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_54 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (41111166212039 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217363800793 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨54, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (41111166212039 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217363800793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_55 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82188735338003 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217367813893 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨55, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82188735338003 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217367813893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_56 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82155161353637 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217371811541 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨56, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82155161353637 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217371811541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_57 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82121610443491 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217375848741 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨57, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82121610443491 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217375848741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_58 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82088082580213 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277172482749 / 12500000000000 : ℝ))
      (E := (cell12990 ⟨58, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82088082580213 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277172482749 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_59 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (10256822217073 / 12500000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217383846717 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨59, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (10256822217073 / 12500000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217383846717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12991_40 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82695118828101 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217193207973 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨40, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82695118828101 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217193207973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_41 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41330597679711 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217197171951 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨41, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41330597679711 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217197171951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_42 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82627295392107 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (22172012157 / 1000000000000 : ℝ))
      (E := (cell12991 ⟨42, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82627295392107 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (22172012157 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_43 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (20648354724167 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (443441044079 / 20000000000000 : ℝ))
      (E := (cell12991 ⟨43, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (20648354724167 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (443441044079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_44 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (20639891460941 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554302310853 / 25000000000000 : ℝ))
      (E := (cell12991 ⟨44, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (20639891460941 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554302310853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_45 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82525736204201 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108606612111 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨45, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82525736204201 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108606612111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_46 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41245964974467 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108608609907 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨46, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41245964974467 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108608609907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_47 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82458147049061 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217221228123 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨47, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82458147049061 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217221228123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_48 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82424387475827 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108612623433 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨48, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82424387475827 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108612623433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_49 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82390651200619 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217229273551 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨49, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82390651200619 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217229273551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_50 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (10294617274371 / 12500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217233305471 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨50, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (10294617274371 / 12500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217233305471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_51 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (20580812107637 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217237280677 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨51, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (20580812107637 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217237280677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_52 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (3291583275167 / 4000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108620657041 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨52, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (3291583275167 / 4000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108620657041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_53 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41127969256401 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108622642131 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨53, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41127969256401 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108622642131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_54 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82222318303527 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217249305807 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨54, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82222318303527 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217249305807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_55 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (2568397538237 / 3125000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (443450663181 / 20000000000000 : ℝ))
      (E := (cell12991 ⟨55, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (2568397538237 / 3125000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (443450663181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_56 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (16431029449069 / 20000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217257369747 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨56, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (16431029449069 / 20000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217257369747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_57 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82121596341321 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217261344887 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨57, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82121596341321 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217261344887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_58 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (256525214013 / 312500000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108632677637 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨58, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (256525214013 / 312500000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108632677637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_59 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (20513640911661 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217269396401 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨59, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (20513640911661 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217269396401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12992_40 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (661560836987 / 800000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108539348353 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨40, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (661560836987 / 800000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108539348353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_41 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (1291580955639 / 1562500000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108541357907 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨41, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (1291580955639 / 1562500000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108541357907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_42 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82627281199777 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443417351193 / 20000000000000 : ℝ))
      (E := (cell12992 ⟨42, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82627281199777 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443417351193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_43 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (645260974301 / 781250000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217090757107 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨43, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (645260974301 / 781250000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217090757107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_44 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82559551663809 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108547388309 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨44, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82559551663809 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108547388309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_45 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82525722030427 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217098753967 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨45, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82525722030427 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217098753967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_46 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (16498383156267 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217102805061 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨46, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (16498383156267 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217102805061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_47 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82458132887633 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (277138351253 / 12500000000000 : ℝ))
      (E := (cell12992 ⟨47, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82458132887633 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (277138351253 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_48 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (20606093330141 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217110825469 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨48, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (20606093330141 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217110825469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_49 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (20597659262879 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443422957983 / 20000000000000 : ℝ))
      (E := (cell12992 ⟨49, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (20597659262879 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443422957983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_50 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82356924052021 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (554279704651 / 25000000000000 : ℝ))
      (E := (cell12992 ⟨50, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82356924052021 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (554279704651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_51 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (10290404286719 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108561424829 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨51, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (10290404286719 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108561424829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_52 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (20572391937131 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (554281705223 / 25000000000000 : ℝ))
      (E := (cell12992 ⟨52, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (20572391937131 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (554281705223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_53 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (20563981097073 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217130847059 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨53, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (20563981097073 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217130847059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_54 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82222304185153 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (110856743279 / 5000000000000 : ℝ))
      (E := (cell12992 ⟨54, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82222304185153 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (110856743279 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_55 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (4109435355567 / 5000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108569436351 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨55, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (4109435355567 / 5000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108569436351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_56 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82155133139227 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108571432231 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨56, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82155133139227 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108571432231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_57 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (3284863289653 / 4000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108573447933 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨57, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (3284863289653 / 4000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108573447933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_58 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (2052201359757 / 2500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108575451707 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨58, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (2052201359757 / 2500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108575451707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_59 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (20513637389719 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217154941747 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨59, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (20513637389719 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217154941747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12993_40 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41347545210419 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443392859727 / 20000000000000 : ℝ))
      (E := (cell12993 ⟨40, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41347545210419 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443392859727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_41 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82661166964559 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216968314123 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨41, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82661166964559 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216968314123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_42 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41313633504817 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108486145939 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨42, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41313633504817 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108486145939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_43 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (3303735621063 / 4000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216976289469 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨43, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (3303735621063 / 4000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216976289469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_44 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (2063988437151 / 2500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108490152737 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨44, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (2063988437151 / 2500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108490152737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_45 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41262853929419 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443396867651 / 20000000000000 : ℝ))
      (E := (cell12993 ⟨45, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41262853929419 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443396867651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_46 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (1031148770199 / 1250000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554247081761 / 25000000000000 : ℝ))
      (E := (cell12993 ⟨46, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (1031148770199 / 1250000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554247081761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_47 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82458118728387 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (6928101027 / 312500000000 : ℝ))
      (E := (cell12993 ⟨47, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82458118728387 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (6928101027 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_48 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82424359167483 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108498170381 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨48, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82424359167483 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108498170381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_49 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (16478124580919 / 20000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108500180459 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨49, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (16478124580919 / 20000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108500180459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_50 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41178454955627 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108502193201 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨50, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41178454955627 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108502193201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_51 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41161610079567 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (277126051787 / 12500000000000 : ℝ))
      (E := (cell12993 ⟨51, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41161610079567 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (277126051787 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_52 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82289553620051 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (138563273901 / 6250000000000 : ℝ))
      (E := (cell12993 ⟨52, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82289553620051 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (138563273901 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_53 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82255910265959 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443403281103 / 20000000000000 : ℝ))
      (E := (cell12993 ⟨53, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82255910265959 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443403281103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_54 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41111145034477 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108510210507 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨54, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41111145034477 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108510210507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_55 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (10273586625159 / 12500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108512212579 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨55, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (10273586625159 / 12500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108512212579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_56 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (20538779758821 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108514236569 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨56, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (20538779758821 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108514236569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_57 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41060784071751 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2217032442507 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨57, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41060784071751 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2217032442507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_58 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (20522010074643 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108518253207 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨58, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (20522010074643 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108518253207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_59 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82054535473279 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554260120689 / 25000000000000 : ℝ))
      (E := (cell12993 ⟨59, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82054535473279 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554260120689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12994_40 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (8269507622049 / 10000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216849896209 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨40, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (8269507622049 / 10000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216849896209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_41 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82661152770409 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216853908079 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨41, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82661152770409 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216853908079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_42 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41313626410839 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (110842894113 / 5000000000000 : ℝ))
      (E := (cell12994 ⟨42, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41313626410839 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (110842894113 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_43 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82593376344807 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216861935169 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨43, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82593376344807 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216861935169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_44 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82559523310457 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216865888847 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨44, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82559523310457 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216865888847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_45 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (10315711711179 / 12500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108434959097 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨45, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (10315711711179 / 12500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108434959097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_46 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82491887452689 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216873962507 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨46, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82491887452689 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216873962507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_47 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (20614526142831 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (138554872549 / 6250000000000 : ℝ))
      (E := (cell12994 ⟨47, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (20614526142831 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (138554872549 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_48 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82424345016583 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108440984817 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨48, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82424345016583 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108440984817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_49 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82390608759853 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216885986563 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨49, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82390608759853 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216885986563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_50 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41178447886333 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (443377989971 / 20000000000000 : ℝ))
      (E := (cell12994 ⟨50, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41178447886333 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (443377989971 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_51 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (16464641205339 / 20000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216893974589 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨51, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (16464641205339 / 20000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216893974589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_52 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (16457907898751 / 20000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216897998653 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨52, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (16457907898751 / 20000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216897998653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_53 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41127948072901 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216902018707 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨53, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41127948072901 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216902018707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_54 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82222275954931 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216906031209 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨54, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82222275954931 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216906031209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_55 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41094339446689 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216910032401 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨55, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41094339446689 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216910032401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_56 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41077552466757 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (554228504581 / 25000000000000 : ℝ))
      (E := (cell12994 ⟨56, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41077552466757 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (554228504581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_57 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82121554047851 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (138557377749 / 6250000000000 : ℝ))
      (E := (cell12994 ⟨57, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82121554047851 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (138557377749 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_58 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (20522006552259 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108461022939 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨58, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (20522006552259 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108461022939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_59 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (20513630347463 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216926078649 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨59, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (20513630347463 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216926078649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12995_40 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (8269506202233 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108367744717 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨40, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (8269506202233 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108367744717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_41 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82661138578447 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (554184874421 / 25000000000000 : ℝ))
      (E := (cell12995 ⟨41, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82661138578447 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (554184874421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_42 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82627238635909 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108371763557 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨42, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82627238635909 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108371763557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_43 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41296681082613 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (88669900707 / 4000000000000 : ℝ))
      (E := (cell12995 ⟨43, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41296681082613 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (88669900707 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_44 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82559509137057 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108375763371 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨44, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82559509137057 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108375763371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_45 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82525679522211 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216755552677 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨45, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82525679522211 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216755552677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_46 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82491873291639 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (277094941839 / 12500000000000 : ℝ))
      (E := (cell12995 ⟨46, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82491873291639 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (277094941839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_47 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41229045208221 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443352717717 / 20000000000000 : ℝ))
      (E := (cell12995 ⟨47, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41229045208221 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443352717717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_48 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82424330867863 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108383797081 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨48, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82424330867863 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108383797081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_49 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82390594617291 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (277096450983 / 12500000000000 : ℝ))
      (E := (cell12995 ⟨49, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82390594617291 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (277096450983 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_50 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82356881636257 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (88671022719 / 4000000000000 : ℝ))
      (E := (cell12995 ⟨50, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82356881636257 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (88671022719 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_51 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82323191896433 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (88671183583 / 4000000000000 : ℝ))
      (E := (cell12995 ⟨51, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82323191896433 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (88671183583 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_52 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (20572381342409 / 25000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216783610549 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨52, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (20572381342409 / 25000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216783610549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_53 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82255882027821 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216787627561 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨53, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82255882027821 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216787627561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_54 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82222261843083 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443358327413 / 20000000000000 : ℝ))
      (E := (cell12995 ⟨54, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82222261843083 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443358327413 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_55 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41094332393829 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108397817653 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨55, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41094332393829 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108397817653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_56 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82155090833917 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108399838737 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨56, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82155090833917 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108399838737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_57 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82121539954373 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216803700297 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨57, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82121539954373 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216803700297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_58 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (10261001515209 / 12500000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216807699401 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨58, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (10261001515209 / 12500000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216807699401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_59 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (20513626827149 / 25000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (34637682347 / 1562500000000 : ℝ))
      (E := (cell12995 ⟨59, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (20513626827149 / 25000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (34637682347 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12996_40 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41347523913179 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108310568541 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨40, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41347523913179 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108310568541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_41 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (1291580068573 / 1562500000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108312570869 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨41, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (1291580068573 / 1562500000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108312570869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_42 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (3305088978093 / 4000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216629167621 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨42, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (3305088978093 / 4000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216629167621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_43 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82593347987829 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216633154679 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨43, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82593347987829 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216633154679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_44 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41279747482921 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221663716029 / 10000000000000 : ℝ))
      (E := (cell12996 ⟨44, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41279747482921 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221663716029 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_45 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (20631416339293 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443328236563 / 20000000000000 : ℝ))
      (E := (cell12996 ⟨45, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (20631416339293 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443328236563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_46 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (20622964783193 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108322580743 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨46, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (20622964783193 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108322580743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_47 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82458076263741 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108324606021 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨47, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82458076263741 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108324606021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_48 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (20606079180331 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108326607173 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨48, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (20606079180331 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108326607173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_49 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82390580476909 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108328612411 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨49, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82390580476909 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108328612411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_50 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41178433751013 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216661240763 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨50, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41178433751013 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216661240763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_51 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82323177768349 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554166314813 / 25000000000000 : ℝ))
      (E := (cell12996 ⟨51, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82323177768349 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554166314813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_52 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41144755623847 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108334638581 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨52, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41144755623847 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108334638581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_53 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (16451173582403 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443334658231 / 20000000000000 : ℝ))
      (E := (cell12996 ⟨53, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (16451173582403 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443334658231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_54 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82222247733409 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216677297687 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨54, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82222247733409 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216677297687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_55 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82188650684111 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216681293001 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨55, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82188650684111 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216681293001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_56 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82155076736493 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108342636569 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨56, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82155076736493 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108342636569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_57 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41060762931533 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108344646551 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨57, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41060762931533 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108344646551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_58 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82087998036477 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216693348591 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨58, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82087998036477 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216693348591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_59 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (8205449322951 / 10000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216697316653 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨59, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (8205449322951 / 10000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216697316653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12997_40 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82695033632573 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216506780381 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨40, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82695033632573 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216506780381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_41 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82661110201083 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216510781443 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨41, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82661110201083 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216510781443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_42 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82627210270927 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108257401889 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨42, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82627210270927 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108257401889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_43 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (10324166726577 / 12500000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216518846181 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨43, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (10324166726577 / 12500000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216518846181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_44 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (8255948079681 / 10000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (55413071209 / 2500000000000 : ℝ))
      (E := (cell12997 ⟨44, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (8255948079681 / 10000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (55413071209 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_45 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16505130238863 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (69266462769 / 3125000000000 : ℝ))
      (E := (cell12997 ⟨45, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16505130238863 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (69266462769 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_46 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41245922488043 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216530842831 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨46, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41245922488043 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216530842831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_47 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82458062113221 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108267415577 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨47, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82458062113221 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108267415577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_48 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16484860515393 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (44330777783 / 2000000000000 : ℝ))
      (E := (cell12997 ⟨48, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16484860515393 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (44330777783 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_49 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16478113267741 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (277067862053 / 12500000000000 : ℝ))
      (E := (cell12997 ⟨49, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16478113267741 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (277067862053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_50 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (20589213342493 / 25000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (221654690921 / 10000000000000 : ℝ))
      (E := (cell12997 ⟨50, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (20589213342493 / 25000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (221654690921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_51 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41161581821221 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216550924589 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨51, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41161581821221 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216550924589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_52 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82289497127927 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (443310987887 / 20000000000000 : ℝ))
      (E := (cell12997 ⟨52, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82289497127927 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (443310987887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_53 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16451170759677 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (221655895041 / 10000000000000 : ℝ))
      (E := (cell12997 ⟨53, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16451170759677 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (221655895041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_54 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (8222223362591 / 10000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216562953969 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨54, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (8222223362591 / 10000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216562953969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_55 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41094318291369 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108283473179 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨55, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41094318291369 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108283473179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_56 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82155062641241 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (443314196553 / 20000000000000 : ℝ))
      (E := (cell12997 ⟨56, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82155062641241 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (443314196553 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_57 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82121511773931 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108287499959 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨57, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82121511773931 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108287499959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_58 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41043991976727 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554144748361 / 25000000000000 : ℝ))
      (E := (cell12997 ⟨58, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41043991976727 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554144748361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_59 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82054479152593 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108291508993 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨59, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82054479152593 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108291508993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12998_40 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (3307800777639 / 4000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108196239053 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨40, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (3307800777639 / 4000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108196239053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_41 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (258315925049 / 312500000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216396475599 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨41, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (258315925049 / 312500000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216396475599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_42 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82627196091713 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554100123603 / 25000000000000 : ℝ))
      (E := (cell12998 ⟨42, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82627196091713 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554100123603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_43 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82593319639587 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216404474493 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨43, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82593319639587 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216404474493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_44 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82559466629961 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108204266043 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨44, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82559466629961 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108204266043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_45 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82525637033641 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216412547841 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨45, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82525637033641 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216412547841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_46 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82491830821581 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216416519833 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨46, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82491830821581 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216416519833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_47 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82458047964881 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108210281901 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨47, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82458047964881 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108210281901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_48 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (2575759013587 / 3125000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216424559613 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨48, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (2575759013587 / 3125000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216424559613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_49 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82390552202679 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108214281843 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨49, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82390552202679 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108214281843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_50 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (2573651226253 / 3125000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216432573317 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨50, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (2573651226253 / 3125000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216432573317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_51 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (8232314951871 / 10000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554109146397 / 25000000000000 : ℝ))
      (E := (cell12998 ⟨51, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (8232314951871 / 10000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554109146397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_52 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (2571546344073 / 3125000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (221644059737 / 10000000000000 : ℝ))
      (E := (cell12998 ⟨52, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (2571546344073 / 3125000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (221644059737 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_53 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (5140989980433 / 6250000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216444605329 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨53, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (5140989980433 / 6250000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216444605329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_54 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (10277777440073 / 12500000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216448605917 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨54, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (10277777440073 / 12500000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216448605917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_55 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82188622483537 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216452654507 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨55, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82188622483537 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216452654507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_56 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82155048548161 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554114157227 / 25000000000000 : ℝ))
      (E := (cell12998 ⟨56, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82155048548161 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554114157227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_57 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (41060748843483 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554115160807 / 25000000000000 : ℝ))
      (E := (cell12998 ⟨57, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (41060748843483 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554115160807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_58 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82087969872599 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443292938633 / 20000000000000 : ℝ))
      (E := (cell12998 ⟨58, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82087969872599 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443292938633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_59 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (16410893015569 / 20000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108234327883 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨59, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (16410893015569 / 20000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108234327883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12999_40 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82695005251563 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554069542871 / 25000000000000 : ℝ))
      (E := (cell12999 ⟨40, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82695005251563 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554069542871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_41 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41330540916231 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216282165409 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨41, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41330540916231 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216282165409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_42 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (20656795478671 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (22162861807 / 1000000000000 : ℝ))
      (E := (cell12999 ⟨42, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (20656795478671 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (22162861807 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_43 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41296652734371 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (44325804323 / 2000000000000 : ℝ))
      (E := (cell12999 ⟨43, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41296652734371 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (44325804323 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_44 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41279726232647 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554073552867 / 25000000000000 : ℝ))
      (E := (cell12999 ⟨44, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41279726232647 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554073552867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_45 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (20631405718787 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216298223839 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨45, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (20631405718787 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216298223839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_46 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82491816669257 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216302251409 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨46, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82491816669257 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216302251409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_47 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (515362711367 / 625000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216306233171 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨47, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (515362711367 / 625000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216306233171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_48 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41212137147391 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108155142349 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨48, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41212137147391 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108155142349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_49 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82390538068831 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (443262857119 / 20000000000000 : ℝ))
      (E := (cell12999 ⟨49, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82390538068831 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (443262857119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_50 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82356825112397 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (17314986657 / 781250000000 : ℝ))
      (E := (cell12999 ⟨50, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82356825112397 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (17314986657 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_51 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (16464627079431 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108161150641 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨51, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (16464627079431 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108161150641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_52 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82289468894919 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108163155013 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨52, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82289468894919 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108163155013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_53 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41127912788823 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (138520644687 / 6250000000000 : ℝ))
      (E := (cell12999 ⟨53, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41127912788823 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (138520644687 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_54 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82222205417431 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216334312633 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨54, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82222205417431 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216334312633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_55 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (20547152096627 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216338358323 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨55, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (20547152096627 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216338358323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_56 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82155034457251 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216342329869 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨56, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82155034457251 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216342329869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_57 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82121483602171 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216346341379 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨57, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82121483602171 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216346341379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_58 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41043977896957 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216350388553 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨58, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41043977896957 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216350388553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_59 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (16410890201053 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108177203829 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨59, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (16410890201053 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108177203829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

end BstLean.Part268
