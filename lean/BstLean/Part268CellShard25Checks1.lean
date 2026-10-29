import BstLean.Part268CellShard25Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12975_20 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83378799830849 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277368451161 / 12500000000000 : ℝ))
      (E := (cell12975 ⟨20, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83378799830849 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277368451161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_21 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83344399804743 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218951607519 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨21, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83344399804743 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218951607519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_22 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (10413752987803 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218955603439 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨22, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (10413752987803 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218955603439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_23 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41637836045621 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109479800181 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨23, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41637836045621 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109479800181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_24 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (10405168042339 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218963601369 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨24, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (10405168042339 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218963601369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_25 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41603520306259 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554741902327 / 25000000000000 : ℝ))
      (E := (cell12975 ⟨25, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41603520306259 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554741902327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_26 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83172760880509 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218971626789 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨26, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83172760880509 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218971626789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_27 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (10392313138837 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109487828099 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨27, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (10392313138837 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109487828099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_28 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83104273271257 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (221897964119 / 10000000000000 : ℝ))
      (E := (cell12975 ⟨28, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83104273271257 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (221897964119 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_29 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83070065330529 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554745910533 / 25000000000000 : ℝ))
      (E := (cell12975 ⟨29, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83070065330529 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554745910533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_30 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (20758970314253 / 25000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554746915179 / 25000000000000 : ℝ))
      (E := (cell12975 ⟨30, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (20758970314253 / 25000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554746915179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_31 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83001721019367 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218991639843 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨31, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83001721019367 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218991639843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_32 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41483792293207 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109497819631 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨32, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41483792293207 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109497819631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_33 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (8293347192713 / 10000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443799931997 / 20000000000000 : ℝ))
      (E := (cell12975 ⟨33, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (8293347192713 / 10000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443799931997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_34 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82899383010651 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443800740559 / 20000000000000 : ℝ))
      (E := (cell12975 ⟨34, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82899383010651 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443800740559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_35 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82865317806269 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219007709597 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨35, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82865317806269 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219007709597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_36 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (10353909535429 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (138688230041 / 6250000000000 : ℝ))
      (E := (cell12975 ⟨36, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (10353909535429 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (138688230041 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_37 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41398629205871 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219015733419 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨37, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41398629205871 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2219015733419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_38 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (16552652832191 / 20000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277377461459 / 12500000000000 : ℝ))
      (E := (cell12975 ⟨38, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (16552652832191 / 20000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277377461459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_39 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (82729293500979 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277377966399 / 12500000000000 : ℝ))
      (E := (cell12975 ⟨39, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (82729293500979 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277377966399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12976_20 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83378785465613 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218832726437 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨20, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83378785465613 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218832726437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_21 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (20836096361457 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218836778177 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨21, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (20836096361457 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218836778177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_22 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (81357431201 / 97656250000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218840769349 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨22, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (81357431201 / 97656250000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218840769349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_23 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (10409457218119 / 12500000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218844761569 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨23, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (10409457218119 / 12500000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218844761569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_24 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (10405166249841 / 12500000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218848757919 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨24, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (10405166249841 / 12500000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218848757919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_25 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41603513139417 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (69339148789 / 3125000000000 : ℝ))
      (E := (cell12976 ⟨25, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41603513139417 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (69339148789 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_26 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41586373276559 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218856774167 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨26, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41586373276559 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218856774167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_27 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (16627698157919 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218860799057 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨27, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (16627698157919 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218860799057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_28 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83104258956439 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218864779579 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨28, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83104258956439 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218864779579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_29 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83070051021989 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218868834613 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨29, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83070051021989 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218868834613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_30 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41517933477373 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218872790303 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨30, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41517933477373 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218872790303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_31 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83001706723369 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218876823659 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨31, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83001706723369 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218876823659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_32 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41483785148339 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218880818817 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨32, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41483785148339 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218880818817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_33 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (82933457643651 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (88755393413 / 4000000000000 : ℝ))
      (E := (cell12976 ⟨33, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (82933457643651 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (88755393413 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_34 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (5181210545839 / 6250000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218888815333 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨34, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (5181210545839 / 6250000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218888815333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_35 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (82865303535289 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554723219161 / 25000000000000 : ℝ))
      (E := (cell12976 ⟨35, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (82865303535289 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554723219161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_36 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (82831262018693 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109448421813 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨36, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (82831262018693 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109448421813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_37 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (2069931103831 / 2500000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218900892359 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨37, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (2069931103831 / 2500000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218900892359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_38 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (20690812477171 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218904846627 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨38, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (20690812477171 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218904846627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_39 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (16545855850987 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (69340902569 / 3125000000000 : ℝ))
      (E := (cell12976 ⟨39, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (16545855850987 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (69340902569 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12977_20 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83378771102593 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218717955807 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨20, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83378771102593 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218717955807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_21 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (10418046386141 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (17333765191 / 781250000000 : ℝ))
      (E := (cell12977 ⟨21, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (10418046386141 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (17333765191 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_22 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (1041374939993 / 1250000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218725930869 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨22, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (1041374939993 / 1250000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218725930869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_23 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83275643400877 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218729976763 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨23, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83275643400877 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218729976763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_24 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83241315660957 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109366984241 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨24, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83241315660957 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109366984241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_25 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83207011947361 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (88749518689 / 4000000000000 : ℝ))
      (E := (cell12977 ⟨25, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83207011947361 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (88749518689 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_26 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83172732227939 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443748395121 / 20000000000000 : ℝ))
      (E := (cell12977 ⟨26, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83172732227939 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443748395121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_27 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83138476470703 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218745996003 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨27, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83138476470703 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218745996003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_28 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (8310424464383 / 10000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109374986039 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨28, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (8310424464383 / 10000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109374986039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_29 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (41535018357829 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554688491049 / 25000000000000 : ℝ))
      (E := (cell12977 ⟨29, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (41535018357829 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554688491049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_30 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (41517926327343 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218757974049 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨30, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (41517926327343 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218757974049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_31 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (10375211553697 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109381001549 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨31, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (10375211553697 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109381001549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_32 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82967556009147 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109382996997 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨32, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82967556009147 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109382996997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_33 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (10366680420297 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218770006287 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨33, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (10366680420297 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218770006287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_34 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (103624193073 / 125000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (55469351019 / 2500000000000 : ℝ))
      (E := (cell12977 ⟨34, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (103624193073 / 125000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (55469351019 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_35 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (82865289266511 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443755607863 / 20000000000000 : ℝ))
      (E := (cell12977 ⟨35, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (82865289266511 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443755607863 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_36 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (20707811939039 / 25000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (22187820609 / 1000000000000 : ℝ))
      (E := (cell12977 ⟨36, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (20707811939039 / 25000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (22187820609 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_37 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (41398614948469 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554696511731 / 25000000000000 : ℝ))
      (E := (cell12977 ⟨37, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (41398614948469 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554696511731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_38 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (20690808914653 / 25000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443758011187 / 20000000000000 : ℝ))
      (E := (cell12977 ⟨38, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (20690808914653 / 25000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443758011187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_39 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (5170579063193 / 6250000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109397043801 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨39, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (5170579063193 / 6250000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109397043801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12978_20 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83378756741789 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (554650780621 / 25000000000000 : ℝ))
      (E := (cell12978 ⟨20, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83378756741789 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (554650780621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_21 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (20836089183661 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218607164659 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨21, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (20836089183661 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218607164659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_22 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83309980851269 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218611146357 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨22, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83309980851269 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218611146357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_23 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (16655125811803 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218615187573 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨23, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (16655125811803 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218615187573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_24 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41620650662699 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218619174661 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨24, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41620650662699 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218619174661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_25 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (832069976181 / 1000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218623168819 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨25, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (832069976181 / 1000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218623168819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_26 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (8317271790497 / 10000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218627172661 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨26, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (8317271790497 / 10000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218627172661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_27 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41569231077011 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109315594283 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨27, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41569231077011 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109315594283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_28 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (8310423033343 / 10000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218635218689 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨28, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (8310423033343 / 10000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218635218689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_29 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41535011205767 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218639206431 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨29, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41535011205767 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218639206431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_30 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41517919178417 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218643211953 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨30, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41517919178417 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218643211953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_31 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83001678137989 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (27733090459 / 1250000000000 : ℝ))
      (E := (cell12978 ⟨31, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83001678137989 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (27733090459 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_32 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (4148377086191 / 5000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (110932561169 / 5000000000000 : ℝ))
      (E := (cell12978 ⟨32, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (4148377086191 / 5000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (110932561169 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_33 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (16586685816661 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109327615741 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨33, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (16586685816661 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109327615741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_34 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (82899340185579 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (221865926181 / 10000000000000 : ℝ))
      (E := (cell12978 ⟨34, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (82899340185579 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (221865926181 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_35 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (16573054999987 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (554665814067 / 25000000000000 : ℝ))
      (E := (cell12978 ⟨35, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (16573054999987 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (554665814067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_36 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (82831233495819 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109333636901 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨36, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (82831233495819 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109333636901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_37 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (20699303910709 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218671255819 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨37, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (20699303910709 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218671255819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_38 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (82763221410739 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218675260871 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨38, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (82763221410739 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218675260871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_39 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (517057817309 / 625000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (138667455539 / 6250000000000 : ℝ))
      (E := (cell12978 ⟨39, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (517057817309 / 625000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (138667455539 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12979_20 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83378742383201 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (55462208577 / 2500000000000 : ℝ))
      (E := (cell12979 ⟨20, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83378742383201 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (55462208577 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_21 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (41672171191187 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (443698476097 / 20000000000000 : ℝ))
      (E := (cell12979 ⟨21, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (41672171191187 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (443698476097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_22 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83309966505313 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218496357459 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨22, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83309966505313 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218496357459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_23 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (41637807359683 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218500393999 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨23, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (41637807359683 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218500393999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_24 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83241286992051 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277313047057 / 12500000000000 : ℝ))
      (E := (cell12979 ⟨24, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83241286992051 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277313047057 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_25 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (1664139665821 / 2000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554627106113 / 25000000000000 : ℝ))
      (E := (cell12979 ⟨25, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (1664139665821 / 2000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554627106113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_26 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83172703584211 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218512423781 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨26, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83172703584211 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218512423781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_27 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83138447839549 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218516435219 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨27, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83138447839549 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218516435219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_28 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (41552108012619 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218520402427 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨28, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (41552108012619 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218520402427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_29 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83070008109617 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (17332222221 / 781250000000 : ℝ))
      (E := (cell12979 ⟨29, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83070008109617 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (17332222221 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_30 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83035824061187 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109264222741 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨30, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83035824061187 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109264222741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_31 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83001663848607 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109266232983 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨31, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83001663848607 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109266232983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_32 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (41483763720349 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (221853644839 / 10000000000000 : ℝ))
      (E := (cell12979 ⟨32, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (41483763720349 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (221853644839 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_33 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82933414806437 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109270226151 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨33, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82933414806437 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109270226151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_34 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (1036241573937 / 1250000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218544478487 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨34, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (1036241573937 / 1250000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218544478487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_35 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82865260735559 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218548468849 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨35, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82865260735559 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218548468849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_36 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82831219237683 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (221855248233 / 10000000000000 : ℝ))
      (E := (cell12979 ⟨36, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82831219237683 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (221855248233 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_37 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82797201390933 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218556519047 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨37, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82797201390933 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218556519047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_38 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (16552641433013 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109280260081 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨38, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (16552641433013 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109280260081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_39 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (82729236529989 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218564485277 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨39, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (82729236529989 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218564485277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12980_20 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83378728026829 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109186808797 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨20, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83378728026829 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109186808797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_21 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83344328032319 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109188825127 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨21, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83344328032319 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109188825127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_22 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83309952161569 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218381622531 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨22, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83309952161569 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218381622531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_23 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83275600381929 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109192827209 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨23, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83275600381929 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109192827209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_24 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (16648254532183 / 20000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218389632269 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨24, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (16648254532183 / 20000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218389632269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_25 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (8320696896621 / 10000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443678735141 / 20000000000000 : ℝ))
      (E := (cell12980 ⟨25, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (8320696896621 / 10000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443678735141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_26 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41586344632831 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (55459941763 / 2500000000000 : ℝ))
      (E := (cell12980 ⟨26, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41586344632831 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (55459941763 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_27 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (20784608381821 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218401677493 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨27, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (20784608381821 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218401677493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_28 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83104201719253 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218405698773 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨28, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83104201719253 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218405698773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_29 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83069993809907 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109204838883 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨29, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83069993809907 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109204838883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_30 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41517904883873 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218413674633 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨30, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41517904883873 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218413674633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_31 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (8300164956143 / 10000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554604422709 / 25000000000000 : ℝ))
      (E := (cell12980 ⟨31, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (8300164956143 / 10000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554604422709 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_32 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82967513159779 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218421727611 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨32, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82967513159779 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218421727611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_33 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82933400531771 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109212863679 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨33, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82933400531771 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109212863679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_34 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82899311646543 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (138651859339 / 6250000000000 : ℝ))
      (E := (cell12980 ⟨34, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82899311646543 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (138651859339 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_35 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (16573049294677 / 20000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (69326054241 / 3125000000000 : ℝ))
      (E := (cell12980 ⟨35, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (16573049294677 / 20000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (69326054241 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_36 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41415602490873 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (138652359073 / 6250000000000 : ℝ))
      (E := (cell12980 ⟨36, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41415602490873 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (138652359073 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_37 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (82797187141229 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218441777903 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨37, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (82797187141229 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218441777903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_38 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (20690798230397 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443689155017 / 20000000000000 : ℝ))
      (E := (cell12980 ⟨38, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (20690798230397 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443689155017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_39 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41364611146367 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109224897531 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨39, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41364611146367 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109224897531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12981_20 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83378713672671 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554564721931 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨20, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83378713672671 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554564721931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_21 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83344313684477 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (55456572891 / 2500000000000 : ℝ))
      (E := (cell12981 ⟨21, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83344313684477 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (55456572891 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_22 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83309937820039 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218266941569 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨22, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83309937820039 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218266941569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_23 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (5204724127919 / 6250000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218270910453 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨23, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (5204724127919 / 6250000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218270910453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_24 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (8324125833199 / 10000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218274942099 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨24, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (8324125833199 / 10000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218274942099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_25 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (4160347732179 / 5000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109139461289 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨25, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (4160347732179 / 5000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109139461289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_26 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83172674949321 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109141485663 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨26, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83172674949321 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109141485663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_27 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (20784604804307 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (443657394771 / 20000000000000 : ℝ))
      (E := (cell12981 ⟨27, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (20784604804307 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (443657394771 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_28 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (3324167496619 / 4000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218290990741 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨28, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (3324167496619 / 4000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218290990741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_29 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41534989756201 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (443658993077 / 20000000000000 : ℝ))
      (E := (cell12981 ⟨29, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41534989756201 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (443658993077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_30 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83035795476509 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554574739487 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨30, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83035795476509 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554574739487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_31 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (10375204409557 / 12500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109151484947 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨31, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (10375204409557 / 12500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109151484947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_32 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82967498881063 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109153501229 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨32, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82967498881063 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109153501229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_33 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (20733346564827 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218310998041 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨33, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (20733346564827 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218310998041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_34 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82899297380327 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554578753997 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨34, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82899297380327 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554578753997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_35 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82865232213411 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554579749551 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨35, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82865232213411 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554579749551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_36 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82831190728009 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109161501817 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨36, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82831190728009 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109161501817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_37 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82797172893723 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218327032391 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨37, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82797172893723 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218327032391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_38 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (82763178680309 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218331025639 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨38, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (82763178680309 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218331025639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_39 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (20682302014419 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (34661485027 / 1562500000000 : ℝ))
      (E := (cell12981 ⟨39, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (20682302014419 / 25000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (34661485027 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12982_20 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83378699320727 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (34658503309 / 1562500000000 : ℝ))
      (E := (cell12982 ⟨20, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83378699320727 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (34658503309 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_21 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83344299338849 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554537058743 / 25000000000000 : ℝ))
      (E := (cell12982 ⟨21, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83344299338849 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554537058743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_22 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (1041374043509 / 1250000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554538049469 / 25000000000000 : ℝ))
      (E := (cell12982 ⟨22, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (1041374043509 / 1250000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554538049469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_23 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (8327557171369 / 10000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554539055121 / 25000000000000 : ℝ))
      (E := (cell12982 ⟨23, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (8327557171369 / 10000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554539055121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_24 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (3329649760211 / 4000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218160247549 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨24, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (3329649760211 / 4000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218160247549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_25 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83206940323159 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218164223493 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨25, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83206940323159 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218164223493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_26 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83172660635189 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109084133877 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨26, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83172660635189 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109084133877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_27 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41569202454689 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109086132921 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨27, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41569202454689 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109086132921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_28 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (5194010819619 / 6250000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218176278331 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨28, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (5194010819619 / 6250000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218176278331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_29 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83069965217103 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218180248627 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨29, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83069965217103 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218180248627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_30 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41517890593739 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218184295427 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨30, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41517890593739 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218184295427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_31 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41500810496843 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218188303141 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨31, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41500810496843 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218188303141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_32 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (1659349692091 / 2000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554548068233 / 25000000000000 : ℝ))
      (E := (cell12982 ⟨32, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (1659349692091 / 2000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554548068233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_33 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41466685994523 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218196322961 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨33, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41466685994523 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218196322961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_34 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82899283116311 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443640067363 / 20000000000000 : ℝ))
      (E := (cell12982 ⟨34, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82899283116311 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443640067363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_35 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (20716304488909 / 25000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277275539373 / 12500000000000 : ℝ))
      (E := (cell12982 ⟨35, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (20716304488909 / 25000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277275539373 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_36 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (8283117647647 / 10000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554552079103 / 25000000000000 : ℝ))
      (E := (cell12982 ⟨36, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (8283117647647 / 10000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (554552079103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_37 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (16559431729683 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218212341213 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨37, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (16559431729683 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218212341213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_38 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (82763164441227 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218216330551 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨38, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (82763164441227 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218216330551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_39 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41364596912407 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109110171389 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨39, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41364596912407 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109110171389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12983_20 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83378684970997 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109014765723 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨20, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83378684970997 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109014765723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_21 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83344284995433 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218033549923 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨21, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83344284995433 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218033549923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_22 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41654954571807 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (443607513301 / 20000000000000 : ℝ))
      (E := (cell12983 ⟨22, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41654954571807 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (443607513301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_23 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83275557382887 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218041584511 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨23, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83275557382887 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218041584511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_24 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83241229680771 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (110902277431 / 5000000000000 : ℝ))
      (E := (cell12983 ⟨24, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83241229680771 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (110902277431 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_25 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83206926004947 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109024789227 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨25, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83206926004947 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109024789227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_26 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (1299572598801 / 1562500000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (443610711961 / 20000000000000 : ℝ))
      (E := (cell12983 ⟨26, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (1299572598801 / 1562500000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (443610711961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_27 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (10392298825467 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109028805961 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨27, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (10392298825467 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109028805961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_28 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41552079407269 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218061620041 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨28, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41552079407269 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218061620041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_29 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83069950924009 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554516396503 / 25000000000000 : ℝ))
      (E := (cell12983 ⟨29, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83069950924009 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554516396503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_30 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (1660715338013 / 2000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218069628533 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨30, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (1660715338013 / 2000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218069628533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_31 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (518760041957 / 625000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (443614726403 / 20000000000000 : ℝ))
      (E := (cell12983 ⟨31, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (518760041957 / 625000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (443614726403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_32 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (82967470330239 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218077597621 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨32, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (82967470330239 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218077597621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_33 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41466678860493 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (221808164351 / 10000000000000 : ℝ))
      (E := (cell12983 ⟨33, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41466678860493 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (221808164351 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_34 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (2590602151703 / 3125000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218085653271 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨34, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (2590602151703 / 3125000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218085653271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_35 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (82865203700061 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218089627393 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨35, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (82865203700061 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218089627393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_36 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (8283116222713 / 10000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218093683501 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨36, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (8283116222713 / 10000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218093683501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_37 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (10349643050663 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554524411417 / 25000000000000 : ℝ))
      (E := (cell12983 ⟨37, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (10349643050663 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554524411417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_38 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (4138157510217 / 5000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109050844913 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨38, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (4138157510217 / 5000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109050844913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_39 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (82729179594147 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109052849107 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨39, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (82729179594147 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109052849107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12984_20 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (2084466765587 / 2500000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (27723936313 / 1250000000000 : ℝ))
      (E := (cell12984 ⟨20, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (2084466765587 / 2500000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (27723936313 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_21 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (8334427065423 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217918918821 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨21, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (8334427065423 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217918918821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_22 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (41654947404359 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554480732689 / 25000000000000 : ℝ))
      (E := (cell12984 ⟨22, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (41654947404359 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554480732689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_23 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (16655108610859 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277240860723 / 12500000000000 : ℝ))
      (E := (cell12984 ⟨23, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (16655108610859 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277240860723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_24 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (3329648614339 / 4000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217930903713 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨24, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (3329648614339 / 4000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217930903713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_25 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (83206911688943 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108967464519 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨25, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (83206911688943 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108967464519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_26 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (83172632013547 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108969452963 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨26, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (83172632013547 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108969452963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_27 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (831383763003 / 1000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217942953627 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨27, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (831383763003 / 1000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217942953627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_28 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (41552072258689 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (34655421209 / 1562500000000 : ℝ))
      (E := (cell12984 ⟨28, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (41552072258689 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (34655421209 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_29 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (519187103957 / 625000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217950977539 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨29, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (519187103957 / 625000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217950977539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_30 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (3321430104641 / 4000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554488739317 / 25000000000000 : ℝ))
      (E := (cell12984 ⟨30, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (3321430104641 / 4000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554488739317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_31 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (16600318486951 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217958956519 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨31, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (16600318486951 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217958956519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_32 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82967456058129 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217962976527 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨32, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82967456058129 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217962976527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_33 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (663466747641 / 800000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554491739923 / 25000000000000 : ℝ))
      (E := (cell12984 ⟨33, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (663466747641 / 800000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (554491739923 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_34 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (259060170609 / 312500000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (27724637067 / 1250000000000 : ℝ))
      (E := (cell12984 ⟨34, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (259060170609 / 312500000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (27724637067 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_35 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (20716297361671 / 25000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217974994093 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨35, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (20716297361671 / 25000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217974994093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_36 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (82831147979987 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277247373443 / 12500000000000 : ℝ))
      (E := (cell12984 ⟨36, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (82831147979987 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277247373443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_37 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (8279713016439 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217983004461 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨37, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (8279713016439 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217983004461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_38 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (1655262719393 / 2000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (443597408947 / 20000000000000 : ℝ))
      (E := (cell12984 ⟨38, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (1655262719393 / 2000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (443597408947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_39 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (3309166614627 / 4000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (443598209857 / 20000000000000 : ℝ))
      (E := (cell12984 ⟨39, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (3309166614627 / 4000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (443598209857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12985_20 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (2605583008693 / 3125000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108900137127 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨20, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (2605583008693 / 3125000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108900137127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_21 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41672128157619 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217804283341 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨21, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41672128157619 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217804283341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_22 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41654940238017 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (554452072657 / 25000000000000 : ℝ))
      (E := (cell12985 ⟨22, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41654940238017 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (554452072657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_23 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (10409441090989 / 12500000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (221781229943 / 10000000000000 : ℝ))
      (E := (cell12985 ⟨23, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (10409441090989 / 12500000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (221781229943 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_24 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (20810300259597 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217816312829 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨24, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (20810300259597 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217816312829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_25 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (83206897375147 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108910137623 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨25, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (83206897375147 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108910137623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_26 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (83172617706037 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108912153059 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨26, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (83172617706037 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108912153059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_27 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (8313836199907 / 10000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108914145479 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨27, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (8313836199907 / 10000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108914145479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_28 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (83104130222423 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (221783234883 / 10000000000000 : ℝ))
      (E := (cell12985 ⟨28, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (83104130222423 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (221783234883 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_29 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41534961172217 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108918153089 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨29, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41534961172217 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108918153089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_30 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (20758934583401 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (221784034017 / 10000000000000 : ℝ))
      (E := (cell12985 ⟨30, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (20758934583401 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (221784034017 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_31 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (83001578158593 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108922167607 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨31, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (83001578158593 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108922167607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_32 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82967441788221 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217848351061 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨32, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82967441788221 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217848351061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_33 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (16586665838293 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217852388723 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨33, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (16586665838293 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217852388723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_34 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82899240337463 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217856390347 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨34, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82899240337463 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217856390347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_35 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41432587597753 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (277232544553 / 12500000000000 : ℝ))
      (E := (cell12985 ⟨35, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41432587597753 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (277232544553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_36 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82831133735041 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217864404581 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨36, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82831133735041 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217864404581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_37 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (10349639490709 / 12500000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (277233552199 / 12500000000000 : ℝ))
      (E := (cell12985 ⟨37, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (10349639490709 / 12500000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (277233552199 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_38 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (16552624347431 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217872395279 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨38, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (16552624347431 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217872395279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_39 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (82729151139397 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217876395993 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨39, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (82729151139397 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217876395993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12986_20 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (20844660483771 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (138605352443 / 6250000000000 : ℝ))
      (E := (cell12986 ⟨20, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (20844660483771 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (138605352443 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_21 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (41672120989229 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217689701811 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨21, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (41672120989229 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217689701811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_22 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83309866145559 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (88707748179 / 4000000000000 : ℝ))
      (E := (cell12986 ⟨22, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83309866145559 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (88707748179 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_23 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (41637757201869 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (22176977087 / 1000000000000 : ℝ))
      (E := (cell12986 ⟨23, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (41637757201869 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (22176977087 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_24 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (8324118672051 / 10000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (34651589337 / 1562500000000 : ℝ))
      (E := (cell12986 ⟨24, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (8324118672051 / 10000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (34651589337 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_25 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83206883063559 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108852837751 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨25, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83206883063559 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108852837751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_26 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83172603400733 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (138606856371 / 6250000000000 : ℝ))
      (E := (cell12986 ⟨26, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83172603400733 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (138606856371 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_27 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16627669540009 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443542748171 / 20000000000000 : ℝ))
      (E := (cell12986 ⟨27, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16627669540009 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443542748171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_28 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (10388014491209 / 12500000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217717735913 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨28, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (10388014491209 / 12500000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217717735913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_29 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (2595934626811 / 3125000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108860873739 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨29, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (2595934626811 / 3125000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108860873739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_30 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16607144810677 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108862859351 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨30, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16607144810677 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108862859351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_31 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (10375195485579 / 12500000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277216221013 / 12500000000000 : ℝ))
      (E := (cell12986 ⟨31, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (10375195485579 / 12500000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277216221013 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_32 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (82967427520513 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443546755963 / 20000000000000 : ℝ))
      (E := (cell12986 ⟨32, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (82967427520513 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443546755963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_33 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16586662986001 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277217219347 / 12500000000000 : ℝ))
      (E := (cell12986 ⟨33, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16586662986001 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277217219347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_34 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16579845216449 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108870876167 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨34, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16579845216449 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108870876167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_35 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (3314606437861 / 4000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217745773047 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨35, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (3314606437861 / 4000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217745773047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_36 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (20707779873073 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217749758573 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨36, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (20707779873073 / 25000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217749758573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_37 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (1655942033783 / 2000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277219220957 / 12500000000000 : ℝ))
      (E := (cell12986 ⟨37, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (1655942033783 / 2000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277219220957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_38 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (41381553753427 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (554439450047 / 25000000000000 : ℝ))
      (E := (cell12986 ⟨38, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (41381553753427 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (554439450047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_39 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (82729136915313 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217761797089 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨39, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (82729136915313 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217761797089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12987_20 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83378627594203 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554392779039 / 25000000000000 : ℝ))
      (E := (cell12987 ⟨20, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83378627594203 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554392779039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_21 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (5209014227743 / 6250000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (17324805593 / 781250000000 : ℝ))
      (E := (cell12987 ⟨21, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (5209014227743 / 6250000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (17324805593 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_22 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41654925908647 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108789556973 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨22, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41654925908647 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108789556973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_23 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83275500081773 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443516622719 / 20000000000000 : ℝ))
      (E := (cell12987 ⟨23, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83275500081773 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443516622719 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_24 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83241172404839 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217587117933 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨24, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83241172404839 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217587117933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_25 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83206868754177 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108795564903 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨25, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83206868754177 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108795564903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_26 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (16634517819527 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554398787957 / 25000000000000 : ℝ))
      (E := (cell12987 ⟨26, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (16634517819527 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554398787957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_27 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (3325533336129 / 4000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (221759912791 / 10000000000000 : ℝ))
      (E := (cell12987 ⟨27, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (3325533336129 / 4000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (221759912791 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_28 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (664832813113 / 800000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (69300097457 / 3125000000000 : ℝ))
      (E := (cell12987 ⟨28, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (664832813113 / 800000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (69300097457 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_29 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83069893773673 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554401781473 / 25000000000000 : ℝ))
      (E := (cell12987 ⟨29, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83069893773673 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554401781473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_30 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (10379463721921 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443522230281 / 20000000000000 : ℝ))
      (E := (cell12987 ⟨30, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (10379463721921 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443522230281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_31 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (10375193701609 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (17740921573 / 800000000000 : ℝ))
      (E := (cell12987 ⟨31, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (10375193701609 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (17740921573 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_32 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (16593482651001 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217619204201 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨32, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (16593482651001 / 20000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217619204201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_33 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (10366662583843 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217623175073 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨33, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (10366662583843 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217623175073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_34 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (3315968473169 / 4000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217627168589 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨34, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (3315968473169 / 4000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217627168589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_35 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (82865146699741 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108815592653 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨35, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (82865146699741 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108815592653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_36 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (82831105251739 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108817612781 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨36, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (82831105251739 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108817612781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_37 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (82797087454823 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554409807691 / 25000000000000 : ℝ))
      (E := (cell12987 ⟨37, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (82797087454823 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (554409807691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_38 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (20690773319687 / 25000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108821600367 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨38, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (20690773319687 / 25000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108821600367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_39 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (82729122693423 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108823626287 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨39, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (82729122693423 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108823626287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12988_20 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41689306627767 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217456530541 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨20, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41689306627767 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217456530541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_21 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (10418026663941 / 12500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217460525621 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨21, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (10418026663941 / 12500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217460525621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_22 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83309837491239 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217464577393 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨22, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83309837491239 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217464577393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_23 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (2602358930063 / 3125000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217468572491 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨23, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (2602358930063 / 3125000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217468572491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_24 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (5202572380711 / 6250000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554368143081 / 25000000000000 : ℝ))
      (E := (cell12988 ⟨24, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (5202572380711 / 6250000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554368143081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_25 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83206854447001 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217476579739 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨25, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83206854447001 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217476579739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_26 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41586287398371 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554370149337 / 25000000000000 : ℝ))
      (E := (cell12988 ⟨26, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41586287398371 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554370149337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_27 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (8313831910861 / 10000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217484569063 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨27, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (8313831910861 / 10000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217484569063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_28 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83104087350781 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (34648259593 / 1562500000000 : ℝ))
      (E := (cell12988 ⟨28, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83104087350781 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (34648259593 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_29 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (20767469872899 / 25000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (221749261697 / 10000000000000 : ℝ))
      (E := (cell12988 ⟨29, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (20767469872899 / 25000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (221749261697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_30 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83035695499553 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217496579739 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨30, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83035695499553 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217496579739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_31 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83001535343313 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217500620779 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨31, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83001535343313 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217500620779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_32 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (5185462436981 / 6250000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217504624221 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨32, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (5185462436981 / 6250000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217504624221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_33 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (82933286413681 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (443501729923 / 20000000000000 : ℝ))
      (E := (cell12988 ⟨33, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (82933286413681 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (443501729923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_34 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41449598789201 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217512639113 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨34, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41449598789201 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217512639113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_35 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41432566227577 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217516651857 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨35, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41432566227577 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217516651857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_36 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41415545506691 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217520629507 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨36, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41415545506691 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217520629507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_37 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (82797073222691 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (221752468951 / 10000000000000 : ℝ))
      (E := (cell12988 ⟨37, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (82797073222691 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (221752468951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_38 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (16552615810567 / 20000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217528655647 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨38, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (16552615810567 / 20000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217528655647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_39 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (3309164338949 / 4000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (22175327037 / 1000000000000 : ℝ))
      (E := (cell12988 ⟨39, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (3309164338949 / 4000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (22175327037 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12989_20 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (3335143956763 / 4000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217341998857 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨20, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (3335143956763 / 4000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217341998857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_21 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41672099490689 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217345989293 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨21, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41672099490689 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217345989293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_22 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (2603431973981 / 3125000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554337509117 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨22, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (2603431973981 / 3125000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554337509117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_23 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (83275471444467 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443470805403 / 20000000000000 : ℝ))
      (E := (cell12989 ⟨23, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (83275471444467 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443470805403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_24 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (83241143780119 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277169752793 / 12500000000000 : ℝ))
      (E := (cell12989 ⟨24, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (83241143780119 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277169752793 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_25 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (5200427508877 / 6250000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (22173620253 / 1000000000000 : ℝ))
      (E := (cell12989 ⟨25, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (5200427508877 / 6250000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (22173620253 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_26 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41586280249027 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108683019249 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨26, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41586280249027 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108683019249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_27 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41569152408099 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217370064319 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨27, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41569152408099 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217370064319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_28 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (83104073064641 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108687023209 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨28, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (83104073064641 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108687023209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_29 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (83069865211721 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554344511291 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨29, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (83069865211721 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554344511291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_30 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41517840612969 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277172757781 / 12500000000000 : ℝ))
      (E := (cell12989 ⟨30, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41517840612969 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277172757781 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_31 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (83001521075953 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217386099131 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨31, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (83001521075953 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217386099131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_32 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (82967384730587 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217390098463 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨32, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (82967384730587 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217390098463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_33 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (2591664754963 / 3125000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108697059897 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨33, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (2591664754963 / 3125000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108697059897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_34 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (82899183329777 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108699052637 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨34, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (82899183329777 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108699052637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_35 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (82865118212763 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217402114047 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨35, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (82865118212763 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217402114047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_36 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (4141553838861 / 5000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217406146453 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨36, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (4141553838861 / 5000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217406146453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_37 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (82797058992753 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277176267987 / 12500000000000 : ℝ))
      (E := (cell12989 ⟨37, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (82797058992753 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277176267987 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_38 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (20690766207279 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (34647096327 / 1562500000000 : ℝ))
      (E := (cell12989 ⟨38, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (20690766207279 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (34647096327 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_39 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (82729094256219 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554354537617 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨39, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (82729094256219 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554354537617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12990_20 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83378584584827 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108613760551 / 50000000000000 : ℝ))
      (E := (cell12990 ⟨20, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83378584584827 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108613760551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_21 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83344184653437 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217231506919 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨21, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83344184653437 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217231506919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_22 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83309808845753 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217235491169 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨22, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83309808845753 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217235491169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_23 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (666203657033 / 800000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108619767771 / 50000000000000 : ℝ))
      (E := (cell12990 ⟨23, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (666203657033 / 800000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108619767771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_24 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (20810282367767 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217243526391 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨24, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (20810282367767 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217243526391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_25 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83206825839267 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108623762457 / 50000000000000 : ℝ))
      (E := (cell12990 ⟨25, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83206825839267 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108623762457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_26 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (8317254620157 / 10000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (88690061349 / 4000000000000 : ℝ))
      (E := (cell12990 ⟨26, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (8317254620157 / 10000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (88690061349 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_27 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83138290525989 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443451111041 / 20000000000000 : ℝ))
      (E := (cell12990 ⟨27, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83138290525989 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443451111041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_28 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (41552029390351 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (221725953301 / 10000000000000 : ℝ))
      (E := (cell12990 ⟨28, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (41552029390351 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (221725953301 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_29 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83069850934047 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277157948253 / 12500000000000 : ℝ))
      (E := (cell12990 ⟨29, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83069850934047 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277157948253 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_30 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (20758916738631 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217267598929 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨30, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (20758916738631 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217267598929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_31 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83001506810793 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108635786559 / 50000000000000 : ℝ))
      (E := (cell12990 ⟨31, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83001506810793 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108635786559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_32 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (3318694818867 / 4000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217275568341 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨32, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (3318694818867 / 4000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217275568341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_33 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82933257906149 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277159948201 / 12500000000000 : ℝ))
      (E := (cell12990 ⟨33, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82933257906149 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277159948201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_34 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (20724792270837 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108641812853 / 50000000000000 : ℝ))
      (E := (cell12990 ⟨34, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (20724792270837 / 25000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108641812853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_35 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82865103972567 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217287630533 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨35, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82865103972567 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217287630533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_36 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82831062543253 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (554322900089 / 25000000000000 : ℝ))
      (E := (cell12990 ⟨36, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82831062543253 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (554322900089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_37 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (5174815297813 / 6250000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217295652627 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨37, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (5174815297813 / 6250000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217295652627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_38 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (82763050607589 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217299669851 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨38, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (82763050607589 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217299669851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_39 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (16545816008181 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217303651627 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨39, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (16545816008181 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217303651627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12991_20 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (20844642563197 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108556519487 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨20, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (20844642563197 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108556519487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_21 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (10418021290963 / 12500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217117020173 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨21, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (10418021290963 / 12500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217117020173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_22 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41654897263161 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217121058203 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨22, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41654897263161 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217121058203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_23 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83275442815989 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108562519849 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨23, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83275442815989 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108562519849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_24 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83241115164223 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554282256517 / 25000000000000 : ℝ))
      (E := (cell12991 ⟨24, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83241115164223 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554282256517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_25 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83206811538707 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108566539291 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨25, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83206811538707 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108566539291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_26 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (8317253190729 / 10000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217137083029 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨26, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (8317253190729 / 10000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217137083029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_27 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (2598071132437 / 3125000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108570520861 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨27, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (2598071132437 / 3125000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108570520861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_28 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41552022249483 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217145073727 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨28, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41552022249483 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217145073727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_29 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41534918329287 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108574532001 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨29, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41534918329287 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108574532001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_30 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (8303565268531 / 10000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108576536353 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨30, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (8303565268531 / 10000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108576536353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_31 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (10375186568479 / 12500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (277144637663 / 12500000000000 : ℝ))
      (E := (cell12991 ⟨31, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (10375186568479 / 12500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (277144637663 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_32 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41483678107481 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108580546221 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨32, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41483678107481 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108580546221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_33 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41466621827839 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (277145638209 / 12500000000000 : ℝ))
      (E := (cell12991 ⟨33, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41466621827839 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (277145638209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_34 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (20724788709779 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (88686765671 / 4000000000000 : ℝ))
      (E := (cell12991 ⟨34, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (20724788709779 / 25000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (88686765671 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_35 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82865089734567 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217173142657 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨35, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82865089734567 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217173142657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_36 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (2070776207787 / 2500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217177167261 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨36, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (2070776207787 / 2500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217177167261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_37 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82797030539457 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108590578499 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨37, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82797030539457 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108590578499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_38 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (16552607277651 / 20000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108592585207 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨38, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (16552607277651 / 20000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108592585207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_39 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (82729065827783 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217189148429 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨39, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (82729065827783 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217189148429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12992_20 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (41689277961479 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108499276237 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨20, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (41689277961479 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108499276237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_21 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (4167207800209 / 5000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (277125323423 / 12500000000000 : ℝ))
      (E := (cell12992 ⟨21, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (4167207800209 / 5000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (277125323423 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_22 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (41654890104549 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108503281257 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨22, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (41654890104549 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108503281257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_23 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (4163771425253 / 5000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217010597861 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨23, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (4163771425253 / 5000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217010597861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_24 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (1300642200931 / 1562500000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (88680583191 / 4000000000000 : ℝ))
      (E := (cell12992 ⟨24, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (1300642200931 / 1562500000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (88680583191 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_25 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (2600212413761 / 3125000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217018569457 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨25, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (2600212413761 / 3125000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217018569457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_26 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (83172517615213 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217022627967 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨26, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (83172517615213 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217022627967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_27 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (4156913097609 / 5000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443405328163 / 20000000000000 : ℝ))
      (E := (cell12992 ⟨27, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (4156913097609 / 5000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443405328163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_28 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (8310403021943 / 10000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217030610081 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨28, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (8310403021943 / 10000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217030610081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_29 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (41534911192651 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (277129331831 / 12500000000000 : ℝ))
      (E := (cell12992 ⟨29, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (41534911192651 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (277129331831 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_30 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (16607127683659 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217038659199 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨30, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (16607127683659 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217038659199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_31 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (8300147828707 / 10000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108521312563 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨31, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (8300147828707 / 10000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108521312563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_32 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82967341960447 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (138565416923 / 6250000000000 : ℝ))
      (E := (cell12992 ⟨32, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82967341960447 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (138565416923 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_33 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (20733307351851 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (138565667499 / 6250000000000 : ℝ))
      (E := (cell12992 ⟨33, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (20733307351851 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (138565667499 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_34 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (41449570298539 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217054653487 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨34, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (41449570298539 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217054653487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_35 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82865075498761 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217058650423 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨35, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82865075498761 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217058650423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_36 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (828310340819 / 1000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (277132833891 / 12500000000000 : ℝ))
      (E := (cell12992 ⟨36, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (828310340819 / 1000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (277132833891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_37 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82797016316099 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443413343143 / 20000000000000 : ℝ))
      (E := (cell12992 ⟨37, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82797016316099 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443413343143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_38 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (10345377771389 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217070725349 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨38, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (10345377771389 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217070725349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_39 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (82729051616851 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217074699627 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨39, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (82729051616851 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2217074699627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12993_20 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (10422317699417 / 12500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (221688411991 / 10000000000000 : ℝ))
      (E := (cell12993 ⟨20, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (10422317699417 / 12500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (221688411991 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_21 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (5209008855179 / 6250000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (88675526009 / 4000000000000 : ℝ))
      (E := (cell12993 ⟨21, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (5209008855179 / 6250000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (88675526009 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_22 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83309765894081 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (277111515101 / 12500000000000 : ℝ))
      (E := (cell12993 ⟨22, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83309765894081 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (277111515101 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_23 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83275414196337 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443379230331 / 20000000000000 : ℝ))
      (E := (cell12993 ⟨23, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83275414196337 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443379230331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_24 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83241086557149 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554225032279 / 25000000000000 : ℝ))
      (E := (cell12993 ⟨24, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83241086557149 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554225032279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_25 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (416033914721 / 500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108452086407 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨25, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (416033914721 / 500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108452086407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_26 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83172503325339 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108454084269 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨26, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83172503325339 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108454084269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_27 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83138247668579 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216912177071 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨27, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83138247668579 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216912177071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_28 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (5194000996381 / 6250000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216916200563 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨28, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (5194000996381 / 6250000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216916200563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_29 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83069808114229 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (138557511401 / 6250000000000 : ℝ))
      (E := (cell12993 ⟨29, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83069808114229 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (138557511401 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_30 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83035624153479 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216924182791 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨30, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83035624153479 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216924182791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_31 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (16600292805701 / 20000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216928203153 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨31, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (16600292805701 / 20000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216928203153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_32 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (2592728990879 / 3125000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443386448947 / 20000000000000 : ℝ))
      (E := (cell12993 ⟨32, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (2592728990879 / 3125000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443386448947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_33 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82933215161327 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216936249937 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨33, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82933215161327 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216936249937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_34 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (20724781589309 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216940219473 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨34, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (20724781589309 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216940219473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_35 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82865061265149 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108472135573 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨35, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82865061265149 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108472135573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_36 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41415509927257 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216948229319 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨36, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41415509927257 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216948229319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_37 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (20699250523733 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216952270079 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨37, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (20699250523733 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216952270079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_38 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82763007956161 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216956275929 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨38, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82763007956161 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216956275929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_39 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (82729037408109 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216960305223 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨39, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (82729037408109 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216960305223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12994_20 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83378527269923 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216769741279 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨20, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83378527269923 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216769741279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_21 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41672063681877 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (277096713587 / 12500000000000 : ℝ))
      (E := (cell12994 ⟨21, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41672063681877 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (277096713587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_22 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83309751581269 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108388866543 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨22, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83309751581269 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108388866543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_23 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83275399889819 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (69274429983 / 3125000000000 : ℝ))
      (E := (cell12994 ⟨23, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83275399889819 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (69274429983 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_24 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41620536128459 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (277098216561 / 12500000000000 : ℝ))
      (E := (cell12994 ⟨24, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41620536128459 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (277098216561 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_25 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83206768650251 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216789771803 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨25, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83206768650251 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216789771803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_26 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83172489037667 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216793763191 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨26, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83172489037667 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216793763191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_27 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83138233387179 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216797767433 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨27, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83138233387179 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216797767433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_28 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41552000833481 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (55420044667 / 2500000000000 : ℝ))
      (E := (cell12994 ⟨28, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41552000833481 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (55420044667 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_29 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (20767448461339 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (138550360271 / 6250000000000 : ℝ))
      (E := (cell12994 ⟨29, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (20767448461339 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (138550360271 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_30 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83035609890861 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216809819101 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨30, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83035609890861 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216809819101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_31 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41500724886069 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (138550861051 / 6250000000000 : ℝ))
      (E := (cell12994 ⟨31, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41500724886069 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (138550861051 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_32 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41483656729003 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (110840890717 / 5000000000000 : ℝ))
      (E := (cell12994 ⟨32, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41483656729003 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (110840890717 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_33 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (20733300229361 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (221682181553 / 10000000000000 : ℝ))
      (E := (cell12994 ⟨33, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (20733300229361 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (221682181553 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_34 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (20724778029897 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108412919867 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨34, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (20724778029897 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108412919867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_35 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82865047033731 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (554207457213 / 25000000000000 : ℝ))
      (E := (cell12994 ⟨35, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82865047033731 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (554207457213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_36 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (2070775140733 / 2500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216833841833 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨36, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (2070775140733 / 2500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216833841833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_37 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82796987875957 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216837878789 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨37, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82796987875957 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216837878789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_38 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (413814968717 / 500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108420940441 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨38, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (413814968717 / 500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108420940441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_39 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (82729023201557 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216845847713 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨39, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (82729023201557 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216845847713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12995_20 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83378512946717 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216655299973 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨20, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83378512946717 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216655299973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_21 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83344113046851 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216659321129 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨21, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83344113046851 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216659321129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_22 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (10413717158833 / 12500000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216663340997 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨22, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (10413717158833 / 12500000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216663340997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_23 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (16655077117101 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (554166840723 / 25000000000000 : ℝ))
      (E := (cell12995 ⟨23, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (16655077117101 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (554166840723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_24 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83241057958891 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108335665747 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨24, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83241057958891 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108335665747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_25 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41603377179253 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108337683213 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨25, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41603377179253 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108337683213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_26 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83172474752197 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216679353479 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨26, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83172474752197 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216679353479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_27 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83138219107979 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (277085419179 / 12500000000000 : ℝ))
      (E := (cell12995 ⟨27, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83138219107979 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (277085419179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_28 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83103987394027 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216687368437 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨28, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83103987394027 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216687368437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_29 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41534889789341 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (554172850103 / 25000000000000 : ℝ))
      (E := (cell12995 ⟨29, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41534889789341 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (554172850103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_30 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83035595630441 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (221669539251 / 10000000000000 : ℝ))
      (E := (cell12995 ⟨30, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83035595630441 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (221669539251 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_31 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83001435517967 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108349702343 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨31, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83001435517967 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108349702343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_32 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (518545620063 / 625000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (88668137527 / 4000000000000 : ℝ))
      (E := (cell12995 ⟨32, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (518545620063 / 625000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (88668137527 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_33 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (82933186675757 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (138544214711 / 6250000000000 : ℝ))
      (E := (cell12995 ⟨33, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (82933186675757 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (138544214711 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_34 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (16579819576827 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108355727819 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨34, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (16579819576827 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108355727819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_35 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41432516402253 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216715440861 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨35, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41432516402253 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216715440861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_36 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41415495703159 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216719449993 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨36, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41415495703159 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216719449993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_37 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41398486829587 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443344696629 / 20000000000000 : ℝ))
      (E := (cell12995 ⟨37, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41398486829587 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443344696629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_38 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (8276297953283 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216727481481 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨38, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (8276297953283 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216727481481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_39 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (16545801799439 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (277091437919 / 12500000000000 : ℝ))
      (E := (cell12995 ⟨39, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (16545801799439 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (277091437919 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12996_20 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83378498625719 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (69266905341 / 3125000000000 : ℝ))
      (E := (cell12996 ⟨20, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83378498625719 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (69266905341 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_21 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41672049366077 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554136246881 / 25000000000000 : ℝ))
      (E := (cell12996 ⟨21, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41672049366077 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554136246881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_22 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83309722962263 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443309800579 / 20000000000000 : ℝ))
      (E := (cell12996 ⟨22, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83309722962263 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443309800579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_23 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (16655074256679 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216552961963 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨23, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (16655074256679 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216552961963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_24 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83241043663067 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216556984537 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨24, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83241043663067 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216556984537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_25 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41603370034481 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216561015111 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨25, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41603370034481 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216561015111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_26 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (1299569694827 / 1562500000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554141249463 / 25000000000000 : ℝ))
      (E := (cell12996 ⟨26, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (1299569694827 / 1562500000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554141249463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_27 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (4156910241549 / 5000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (110828449677 / 5000000000000 : ℝ))
      (E := (cell12996 ⟨27, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (4156910241549 / 5000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (110828449677 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_28 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (20775993280823 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108286502163 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨28, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (20775993280823 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108286502163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_29 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (16613953062841 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216577032129 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨29, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (16613953062841 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216577032129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_30 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83035581372219 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (22165810201 / 1000000000000 : ℝ))
      (E := (cell12996 ⟨30, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83035581372219 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (22165810201 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_31 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83001421265993 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554146257049 / 25000000000000 : ℝ))
      (E := (cell12996 ⟨31, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83001421265993 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554146257049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_32 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82967284964349 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554147264413 / 25000000000000 : ℝ))
      (E := (cell12996 ⟨32, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82967284964349 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554147264413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_33 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (10366646554533 / 12500000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216593050867 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨33, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (10366646554533 / 12500000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216593050867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_34 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (663192669207 / 800000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216597067187 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨34, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (663192669207 / 800000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216597067187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_35 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82865018577473 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108300553587 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨35, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82865018577473 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108300553587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_36 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (20707744296377 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (13853781953 / 625000000000 : ℝ))
      (E := (cell12996 ⟨36, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (20707744296377 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (13853781953 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_37 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82796959444581 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216609083149 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨37, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82796959444581 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216609083149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_38 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82762965324449 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216613136457 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨38, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82762965324449 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216613136457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_39 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (82728994795021 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221661709589 / 10000000000000 : ℝ))
      (E := (cell12996 ⟨39, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (82728994795021 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221661709589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12997_20 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41689242153463 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216426637483 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨20, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41689242153463 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216426637483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_21 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83344084419663 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (138526915597 / 6250000000000 : ℝ))
      (E := (cell12997 ⟨21, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83344084419663 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (138526915597 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_22 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83309708656067 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216434660427 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨22, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83309708656067 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216434660427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_23 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83275356983489 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554109653761 / 25000000000000 : ℝ))
      (E := (cell12997 ⟨23, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83275356983489 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554109653761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_24 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41620514684723 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108221316607 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨24, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41620514684723 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108221316607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_25 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (4160336289081 / 5000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (277055832429 / 12500000000000 : ℝ))
      (E := (cell12997 ⟨25, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (4160336289081 / 5000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (277055832429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_26 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (4158622309393 / 5000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108225318931 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨26, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (4158622309393 / 5000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108225318931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_27 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (4156909527809 / 5000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554113671939 / 25000000000000 : ℝ))
      (E := (cell12997 ⟨27, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (4156909527809 / 5000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554113671939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_28 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (20775989713689 / 25000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554114673587 / 25000000000000 : ℝ))
      (E := (cell12997 ⟨28, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (20775989713689 / 25000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554114673587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_29 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83069751051927 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216462718003 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨29, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83069751051927 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216462718003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_30 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83035567116193 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (138529168867 / 6250000000000 : ℝ))
      (E := (cell12997 ⟨30, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83035567116193 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (138529168867 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_31 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16600281403243 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216470705913 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨31, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16600281403243 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216470705913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_32 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82967270720813 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (13852967071 / 625000000000 : ℝ))
      (E := (cell12997 ⟨32, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82967270720813 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (13852967071 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_33 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16586631639793 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216478720611 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨33, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16586631639793 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216478720611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_34 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (2590595919369 / 3125000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (443296546603 / 20000000000000 : ℝ))
      (E := (cell12997 ⟨34, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (2590595919369 / 3125000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (443296546603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_35 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82865004352633 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216486769131 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨35, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82865004352633 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216486769131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_36 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82830962966889 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216490770613 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨36, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82830962966889 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216490770613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_37 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41398472616089 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (69265460547 / 3125000000000 : ℝ))
      (E := (cell12997 ⟨37, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41398472616089 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (69265460547 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_38 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (82762951118257 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (55412469677 / 2500000000000 : ℝ))
      (E := (cell12997 ⟨38, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (82762951118257 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (55412469677 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_39 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16545796119007 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (110825140079 / 5000000000000 : ℝ))
      (E := (cell12997 ⟨39, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16545796119007 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (110825140079 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12998_20 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (4168923499517 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216312299689 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨20, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (4168923499517 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216312299689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_21 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (83344070109377 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443263261443 / 20000000000000 : ℝ))
      (E := (cell12998 ⟨21, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (83344070109377 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443263261443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_22 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (20827423588019 / 25000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216320313593 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨22, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (20827423588019 / 25000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216320313593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_23 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (83275342685787 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108162161069 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨23, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (83275342685787 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108162161069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_24 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (83241015078027 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (221632833593 / 10000000000000 : ℝ))
      (E := (cell12998 ⟨24, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (83241015078027 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (221632833593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_25 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (83206711496479 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443266471563 / 20000000000000 : ℝ))
      (E := (cell12998 ⟨25, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (83206711496479 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443266471563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_26 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (649784624289 / 781250000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216336331959 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨26, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (649784624289 / 781250000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216336331959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_27 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (4156908814179 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216340377613 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨27, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (4156908814179 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216340377613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_28 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (41551972294209 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216344380011 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨28, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (41551972294209 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216344380011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_29 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (41534868395923 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216348399519 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨29, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (41534868395923 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216348399519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_30 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (20758888215591 / 25000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216352379287 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨30, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (20758888215591 / 25000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216352379287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_31 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (83001392768633 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (277044547409 / 12500000000000 : ℝ))
      (E := (cell12998 ⟨31, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (83001392768633 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (277044547409 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_32 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (5185453529967 / 6250000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216360400711 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨32, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (5185453529967 / 6250000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216360400711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_33 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (4146657198193 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216364386001 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨33, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (4146657198193 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216364386001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_34 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82899055190933 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (221636839449 / 10000000000000 : ℝ))
      (E := (cell12998 ⟨34, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82899055190933 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (221636839449 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_35 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (1294765470781 / 1562500000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (138523276671 / 6250000000000 : ℝ))
      (E := (cell12998 ⟨35, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (1294765470781 / 1562500000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (138523276671 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_36 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (4141547437523 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443275284879 / 20000000000000 : ℝ))
      (E := (cell12998 ⟨36, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (4141547437523 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443275284879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_37 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (16559386204393 / 20000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216380446213 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨37, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (16559386204393 / 20000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216380446213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_38 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (41381468457127 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108192216677 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨38, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (41381468457127 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108192216677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_39 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (82728966397237 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (277048555521 / 12500000000000 : ℝ))
      (E := (cell12998 ⟨39, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (82728966397237 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (277048555521 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12999_20 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (2084461391899 / 2500000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (443239603167 / 20000000000000 : ℝ))
      (E := (cell12999 ⟨20, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (2084461391899 / 2500000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (443239603167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_21 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (16668811160259 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554050504711 / 25000000000000 : ℝ))
      (E := (cell12999 ⟨21, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (16668811160259 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554050504711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_22 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83309680050287 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216206020751 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨22, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83309680050287 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216206020751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_23 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41637664195143 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (277026253109 / 12500000000000 : ℝ))
      (E := (cell12999 ⟨23, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41637664195143 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (277026253109 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_24 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83241000788809 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (443242806857 / 20000000000000 : ℝ))
      (E := (cell12999 ⟨24, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83241000788809 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (443242806857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_25 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83206697213539 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108109025919 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨25, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83206697213539 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108109025919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_26 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (20793104408081 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216222080143 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨26, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (20793104408081 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216222080143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_27 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41569081006589 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216226063111 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨27, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41569081006589 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216226063111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_28 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41551965162139 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554057515329 / 25000000000000 : ℝ))
      (E := (cell12999 ⟨28, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41551965162139 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554057515329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_29 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41534861266981 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216234076677 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨29, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41534861266981 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216234076677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_30 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83035538610731 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216238110887 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨30, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83035538610731 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216238110887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_31 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (16600275704649 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108121053421 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨31, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (16600275704649 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108121053421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_32 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (20741810560081 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216246124297 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨32, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (20741810560081 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216246124297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_33 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82933129730947 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216250105649 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨33, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82933129730947 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216250105649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_34 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (331596163857 / 400000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108127055123 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨34, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (331596163857 / 400000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108127055123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_35 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41432487954763 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216258138647 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨35, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41432487954763 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216258138647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_36 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41415467268111 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216262132507 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨36, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41415467268111 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216262132507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_37 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82796916813941 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554066537643 / 25000000000000 : ℝ))
      (E := (cell12999 ⟨37, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82796916813941 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (554066537643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_38 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (82762922712439 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216270134007 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨38, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (82762922712439 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216270134007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_39 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41364476100813 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216274141161 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨39, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41364476100813 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216274141161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

end BstLean.Part268
