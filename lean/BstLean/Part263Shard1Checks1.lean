import BstLean.Part263Shard1Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12250_20 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83385323285549 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311448124701 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨20, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83385323285549 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311448124701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_21 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83350696266557 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155726039143 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨21, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83350696266557 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155726039143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_22 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83316093688147 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155728041257 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨22, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83316093688147 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155728041257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_23 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (8328151551703 / 10000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311460083713 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨23, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (8328151551703 / 10000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311460083713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_24 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (20811740430023 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311464086199 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨24, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (20811740430023 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311464086199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_25 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (20803108066097 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (288933504463 / 12500000000000 : ℝ))
      (E := (cell12250 ⟨25, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (20803108066097 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (288933504463 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_26 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (10397240889643 / 12500000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311472052743 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨26, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (10397240889643 / 12500000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311472052743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_27 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41571723122877 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311476024201 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨27, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41571723122877 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311476024201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_28 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41554494808889 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (115574003511 / 5000000000000 : ℝ))
      (E := (cell12250 ⟨28, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41554494808889 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (115574003511 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_29 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41537278600473 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155742009339 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨29, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41537278600473 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155742009339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_30 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (1660802979263 / 2000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155744023869 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨30, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (1660802979263 / 2000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155744023869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_31 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (1660115297449 / 2000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311492043161 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨31, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (1660115297449 / 2000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311492043161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_32 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41485702448533 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (57787400183 / 2500000000000 : ℝ))
      (E := (cell12250 ⟨32, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41485702448533 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (57787400183 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_33 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (82937069005383 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311500000891 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨33, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (82937069005383 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311500000891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_34 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41451378582973 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (9029312601 / 390625000000 : ℝ))
      (E := (cell12250 ⟨34, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41451378582973 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (9029312601 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_35 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41434234673731 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (288938503173 / 12500000000000 : ℝ))
      (E := (cell12250 ⟨35, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41434234673731 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (288938503173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_36 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (20708551379699 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311512000931 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨36, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (20708551379699 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311512000931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_37 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (82799965648973 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (577879003089 / 25000000000000 : ℝ))
      (E := (cell12250 ⟨37, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (82799965648973 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (577879003089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_38 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (3310629988287 / 4000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311520002079 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨38, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (3310629988287 / 4000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311520002079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_39 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (82731557662741 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311523970877 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨39, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (82731557662741 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311523970877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12251_20 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (41692656851021 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (72228152827 / 3125000000000 : ℝ))
      (E := (cell12251 ⟨20, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (41692656851021 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (72228152827 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_21 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83350687012037 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577826213493 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨21, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83350687012037 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577826213493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_22 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83316084762151 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577827217227 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨22, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83316084762151 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577827217227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_23 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (832815069191 / 1000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155656440797 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨23, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (832815069191 / 1000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155656440797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_24 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (8324695344977 / 10000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311316838023 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨24, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (8324695344977 / 10000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311316838023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_25 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (16642484864243 / 20000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155660429451 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨25, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (16642484864243 / 20000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155660429451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_26 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (10397239937583 / 12500000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577831207849 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨26, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (10397239937583 / 12500000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577831207849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_27 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (8314343895551 / 10000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311328817437 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨27, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (8314343895551 / 10000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311328817437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_28 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (20777245663329 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577833205099 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨28, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (20777245663329 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577833205099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_29 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83074550561811 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311336843409 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨29, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83074550561811 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311336843409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_30 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83040142648889 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155670415457 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨30, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83040142648889 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155670415457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_31 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (8300575888261 / 10000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311344785511 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨31, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (8300575888261 / 10000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311344785511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_32 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (20742849807799 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577837206649 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨32, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (20742849807799 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577837206649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_33 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82937063663031 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311352780841 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨33, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82937063663031 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311352780841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_34 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (10362844018333 / 12500000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577839206441 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨34, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (10362844018333 / 12500000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577839206441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_35 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (207171161627 / 250000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155680393719 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨35, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (207171161627 / 250000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155680393719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_36 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82834201144307 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311364784461 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨36, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82834201144307 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311364784461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_37 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82799961596209 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155684379751 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨37, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82799961596209 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155684379751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_38 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82765745975689 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311372772217 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨38, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82765745975689 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311372772217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_39 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (82731554252087 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311376764777 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨39, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (82731554252087 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311376764777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12252_20 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83385304120351 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155576884101 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨20, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83385304120351 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155576884101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_21 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (8335067775929 / 10000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577789435431 / 25000000000000 : ℝ))
      (E := (cell12252 ⟨21, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (8335067775929 / 10000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577789435431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_22 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83316075837889 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155580883727 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨22, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83316075837889 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155580883727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_23 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83281498322863 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (288895716677 / 12500000000000 : ℝ))
      (E := (cell12252 ⟨23, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83281498322863 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (288895716677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_24 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (41623472590549 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155584880253 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨24, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (41623472590549 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155584880253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_25 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (20803104094913 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311173736173 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨25, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (20803104094913 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311173736173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_26 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (10397238985719 / 12500000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311177722561 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨26, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (10397238985719 / 12500000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311177722561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_27 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83143431666793 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155590861637 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨27, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83143431666793 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155590861637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_28 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (4155448784517 / 5000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155592841631 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨28, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (4155448784517 / 5000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155592841631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_29 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83074543924121 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311189722477 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨29, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83074543924121 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311189722477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_30 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (2595004260501 / 3125000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577798417123 / 25000000000000 : ℝ))
      (E := (cell12252 ⟨30, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (2595004260501 / 3125000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577798417123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_31 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (41502876447067 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155598849653 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨31, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (41502876447067 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155598849653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_32 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (10371424195831 / 12500000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (462240340081 / 20000000000000 : ℝ))
      (E := (cell12252 ⟨32, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (10371424195831 / 12500000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (462240340081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_33 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (82937058321963 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577801418481 / 25000000000000 : ℝ))
      (E := (cell12252 ⟨33, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (82937058321963 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577801418481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_34 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (5181421695539 / 6250000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155604840167 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨34, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (5181421695539 / 6250000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155604840167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_35 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (4143422997767 / 5000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311213662803 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨35, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (4143422997767 / 5000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311213662803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_36 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (41417098385489 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311217681393 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨36, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (41417098385489 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311217681393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_37 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (20699989386141 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311221678769 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨37, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (20699989386141 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311221678769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_38 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (41382871122641 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (462245131187 / 20000000000000 : ℝ))
      (E := (cell12252 ⟨38, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (41382871122641 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (462245131187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_39 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (10341443855309 / 12500000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311229672343 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨39, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (10341443855309 / 12500000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311229672343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12253_20 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (20846323635119 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311006699683 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨20, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (20846323635119 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311006699683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_21 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41675334254159 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311010741539 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨21, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41675334254159 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311010741539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_22 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (520725418221 / 625000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311014719877 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨22, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (520725418221 / 625000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311014719877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_23 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (83281489728317 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155509348741 / 50000000000000 : ℝ))
      (E := (cell12253 ⟨23, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (83281489728317 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155509348741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_24 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (83246936914077 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231102267867 / 10000000000000 : ℝ))
      (E := (cell12253 ⟨24, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (83246936914077 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231102267867 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_25 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41606204219849 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155513333759 / 50000000000000 : ℝ))
      (E := (cell12253 ⟨25, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41606204219849 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155513333759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_26 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (10397238034051 / 12500000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462206133573 / 20000000000000 : ℝ))
      (E := (cell12253 ⟨26, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (10397238034051 / 12500000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462206133573 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_27 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (20785856094901 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462206936663 / 20000000000000 : ℝ))
      (E := (cell12253 ⟨27, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (20785856094901 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462206936663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_28 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (1662179374577 / 2000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311038658817 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨28, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (1662179374577 / 2000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311038658817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_29 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (20768634321969 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (57776066397 / 2500000000000 : ℝ))
      (E := (cell12253 ⟨29, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (20768634321969 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (57776066397 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_30 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (83040130024579 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462209335481 / 20000000000000 : ℝ))
      (E := (cell12253 ⟨30, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (83040130024579 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462209335481 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_31 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (83005746907021 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231105066757 / 10000000000000 : ℝ))
      (E := (cell12253 ⟨31, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (83005746907021 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231105066757 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_32 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (1296427935991 / 1562500000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462210925749 / 20000000000000 : ℝ))
      (E := (cell12253 ⟨32, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (1296427935991 / 1562500000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462210925749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_33 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (2591782905693 / 3125000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462211724321 / 20000000000000 : ℝ))
      (E := (cell12253 ⟨33, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (2591782905693 / 3125000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462211724321 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_34 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (3316109684473 / 4000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (36110353877 / 1562500000000 : ℝ))
      (E := (cell12253 ⟨34, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (3316109684473 / 4000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (36110353877 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_35 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (2071711381527 / 2500000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311066651481 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨35, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (2071711381527 / 2500000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2311066651481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_36 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82834192398809 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155535316559 / 50000000000000 : ℝ))
      (E := (cell12253 ⟨36, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82834192398809 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155535316559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_37 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82799953494039 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (288884324283 / 12500000000000 : ℝ))
      (E := (cell12253 ⟨37, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82799953494039 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (288884324283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_38 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41382869257977 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (144442412161 / 6250000000000 : ℝ))
      (E := (cell12253 ⟨38, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41382869257977 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (144442412161 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_39 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (82731547433897 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155541317449 / 50000000000000 : ℝ))
      (E := (cell12253 ⟨39, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (82731547433897 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155541317449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12254_20 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (5211580310151 / 6250000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155429900687 / 50000000000000 : ℝ))
      (E := (cell12254 ⟨20, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (5211580310151 / 6250000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155429900687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_21 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (1041883240739 / 1250000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310863795167 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨21, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (1041883240739 / 1250000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310863795167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_22 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83316057994563 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310867784457 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨22, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83316057994563 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310867784457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_23 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41640740567731 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462174354759 / 20000000000000 : ℝ))
      (E := (cell12254 ⟨23, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41640740567731 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462174354759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_24 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41623464324353 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (288859470937 / 12500000000000 : ℝ))
      (E := (cell12254 ⟨24, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41623464324353 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (288859470937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_25 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (10401550062669 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310879769637 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨25, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (10401550062669 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310879769637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_26 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (10397237082579 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310883725683 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨26, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (10397237082579 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310883725683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_27 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83143417093941 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (57772193899 / 2500000000000 : ℝ))
      (E := (cell12254 ⟨27, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83143417093941 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (57772193899 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_28 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (16621792353769 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155445873533 / 50000000000000 : ℝ))
      (E := (cell12254 ⟨28, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (16621792353769 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155445873533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_29 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (20768632663269 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462179140413 / 20000000000000 : ℝ))
      (E := (cell12254 ⟨29, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (20768632663269 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462179140413 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_30 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (8304012371453 / 10000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462179936451 / 20000000000000 : ℝ))
      (E := (cell12254 ⟨30, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (8304012371453 / 10000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462179936451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_31 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (8300574092127 / 10000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (36107870161 / 1562500000000 : ℝ))
      (E := (cell12254 ⟨31, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (8300574092127 / 10000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (36107870161 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_32 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (82971382241521 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (288863458767 / 12500000000000 : ℝ))
      (E := (cell12254 ⟨32, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (82971382241521 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (288863458767 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_33 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (8293704764367 / 10000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (92436467297 / 4000000000000 : ℝ))
      (E := (cell12254 ⟨33, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (8293704764367 / 10000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (92436467297 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_34 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41451368548133 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310915670589 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨34, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41451368548133 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310915670589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_35 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (4143422528401 / 5000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310919694891 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨35, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (4143422528401 / 5000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310919694891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_36 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (414170940139 / 500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310923698247 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨36, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (414170940139 / 500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310923698247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_37 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (82799949444633 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310927681883 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨37, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (82799949444633 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310927681883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_38 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41382867393853 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310931646797 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨38, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41382867393853 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310931646797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_39 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (2068288600659 / 2500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577733913111 / 25000000000000 : ℝ))
      (E := (cell12254 ⟨39, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (2068288600659 / 2500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577733913111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12255_20 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (8338527538617 / 10000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155356449291 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨20, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (8338527538617 / 10000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155356449291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_21 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (16670130002339 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (231071690261 / 10000000000000 : ℝ))
      (E := (cell12255 ⟨21, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (16670130002339 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (231071690261 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_22 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41658024537749 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310720902917 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨22, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41658024537749 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310720902917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_23 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41640736272149 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155362452027 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨23, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41640736272149 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155362452027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_24 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (10405865048123 / 12500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155364455167 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨24, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (10405865048123 / 12500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155364455167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_25 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (16642478512923 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155366433743 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨25, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (16642478512923 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155366433743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_26 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41588944525211 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310736896019 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨26, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41588944525211 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310736896019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_27 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (20785852452451 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155370441407 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨27, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (20785852452451 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155370441407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_28 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (3324358192413 / 4000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310744831171 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨28, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (3324358192413 / 4000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310744831171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_29 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (2076863100493 / 2500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155374430517 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨29, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (2076863100493 / 2500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155374430517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_30 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (16608023481177 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (462150571689 / 20000000000000 : ℝ))
      (E := (cell12255 ⟨30, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (16608023481177 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (462150571689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_31 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (83005734936883 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310756825999 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨31, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (83005734936883 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310756825999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_32 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (4148568829047 / 5000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (9026409471 / 390625000000 : ℝ))
      (E := (cell12255 ⟨32, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (4148568829047 / 5000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (9026409471 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_33 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41468521153223 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155382398923 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨33, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41468521153223 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155382398923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_34 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (82902732081949 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310768806277 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨34, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (82902732081949 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310768806277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_35 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (258963893363 / 312500000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155386396517 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨35, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (258963893363 / 312500000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155386396517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_36 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (1656683673159 / 2000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155388409087 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨36, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (1656683673159 / 2000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155388409087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_37 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41399972698173 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (462156164873 / 20000000000000 : ℝ))
      (E := (cell12255 ⟨37, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41399972698173 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (462156164873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_38 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (10345716382567 / 12500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155392406301 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨38, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (10345716382567 / 12500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155392406301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_39 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (82731540619861 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310788783663 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨39, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (82731540619861 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310788783663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12256_20 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41692632905869 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310566107771 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨20, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41692632905869 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310566107771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_21 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41675320383021 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577642530531 / 25000000000000 : ℝ))
      (E := (cell12256 ⟨21, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41675320383021 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577642530531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_22 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (20829010039541 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310574133537 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨22, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (20829010039541 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310574133537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_23 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (10410182994353 / 12500000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (115528904413 / 5000000000000 : ℝ))
      (E := (cell12256 ⟨23, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (10410182994353 / 12500000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (115528904413 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_24 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (8324691212291 / 10000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155291053593 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨24, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (8324691212291 / 10000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155291053593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_25 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41606192314743 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310586077761 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨25, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41606192314743 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310586077761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_26 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (4158894072089 / 5000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (18484720497 / 800000000000 : ℝ))
      (E := (cell12256 ⟨26, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (4158894072089 / 5000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (18484720497 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_27 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (10392925315899 / 12500000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310594063879 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨27, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (10392925315899 / 12500000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310594063879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_28 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (8310894785329 / 10000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (231059808639 / 10000000000000 : ℝ))
      (E := (cell12256 ⟨28, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (8310894785329 / 10000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (231059808639 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_29 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (83074517387807 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462120414869 / 20000000000000 : ℝ))
      (E := (cell12256 ⟨29, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (83074517387807 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462120414869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_30 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41520055549321 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310606089041 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨30, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41520055549321 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310606089041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_31 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (83005728953857 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (72206564833 / 3125000000000 : ℝ))
      (E := (cell12256 ⟨31, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (83005728953857 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (72206564833 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_32 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82971370921681 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155307016777 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨32, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82971370921681 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155307016777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_33 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41468518485251 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (288827253301 / 12500000000000 : ℝ))
      (E := (cell12256 ⟨33, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41468518485251 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (288827253301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_34 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82902727068871 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155311027597 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨34, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82902727068871 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155311027597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_35 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (165736882371 / 200000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310626063077 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨35, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (165736882371 / 200000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310626063077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_36 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82834179289259 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577657512877 / 25000000000000 : ℝ))
      (E := (cell12256 ⟨36, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82834179289259 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577657512877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_37 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41399970674589 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310634021709 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨37, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41399970674589 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310634021709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_38 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (20691431833611 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462127606667 / 20000000000000 : ℝ))
      (E := (cell12256 ⟨38, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (20691431833611 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462127606667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_39 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (82731537214401 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310642028551 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨39, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (82731537214401 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310642028551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12257_20 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (1042315702989 / 1250000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310419428943 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨20, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (1042315702989 / 1250000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310419428943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_21 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41675315761081 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310423453709 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨21, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41675315761081 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310423453709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_22 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41658015621281 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (57760685451 / 2500000000000 : ℝ))
      (E := (cell12257 ⟨22, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41658015621281 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (57760685451 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_23 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83281455367039 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (115521572151 / 5000000000000 : ℝ))
      (E := (cell12257 ⟨23, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83281455367039 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (115521572151 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_24 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41623451931243 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155217708189 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨24, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41623451931243 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155217708189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_25 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83212376695963 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310439400467 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨25, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83212376695963 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310439400467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_26 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83177873834703 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (577610849781 / 25000000000000 : ℝ))
      (E := (cell12257 ⟨26, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83177873834703 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (577610849781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_27 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41571697623053 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310447415949 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨27, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41571697623053 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310447415949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_28 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (4155447044887 / 5000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155225697943 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨28, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (4155447044887 / 5000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155225697943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_29 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41537255378669 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155227700221 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨29, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41537255378669 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155227700221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_30 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83040104792801 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (72201855439 / 3125000000000 : ℝ))
      (E := (cell12257 ⟨30, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83040104792801 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (72201855439 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_31 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83005722972193 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (577615844447 / 25000000000000 : ℝ))
      (E := (cell12257 ⟨31, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83005722972193 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (577615844447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_32 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41485682631871 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155233677793 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨32, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41485682631871 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155233677793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_33 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41468515817919 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (144404460507 / 6250000000000 : ℝ))
      (E := (cell12257 ⟨33, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41468515817919 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (144404460507 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_34 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82902722057033 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155237679391 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨34, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82902722057033 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155237679391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_35 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82868436496039 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288809916159 / 12500000000000 : ℝ))
      (E := (cell12257 ⟨35, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82868436496039 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288809916159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_36 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82834174921727 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155241669821 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨36, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82834174921727 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155241669821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_37 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82799937303129 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310487332551 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨37, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82799937303129 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310487332551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_38 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (82765723609431 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310491308999 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨38, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (82765723609431 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310491308999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_39 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41365766904989 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (577623832109 / 25000000000000 : ℝ))
      (E := (cell12257 ⟨39, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41365766904989 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (577623832109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12258_20 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (20846311667079 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462054560773 / 20000000000000 : ℝ))
      (E := (cell12258 ⟨20, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (20846311667079 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462054560773 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_21 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83350622280053 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310276839113 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨21, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83350622280053 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310276839113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_22 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83316022328689 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155140407353 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨22, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83316022328689 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155140407353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_23 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (5205090423809 / 6250000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155142396713 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨23, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (5205090423809 / 6250000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155142396713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_24 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83246895603709 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462057755917 / 20000000000000 : ℝ))
      (E := (cell12258 ⟨24, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83246895603709 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462057755917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_25 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (5200773047753 / 6250000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155146388627 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨25, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (5200773047753 / 6250000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155146388627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_26 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83177866229193 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310296790269 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨26, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83177866229193 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310296790269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_27 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (16628677593309 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155150381917 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨27, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (16628677593309 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155150381917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_28 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83108933943673 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310304759661 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨28, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83108933943673 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310304759661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_29 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (10384313016039 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310308780883 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨29, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (10384313016039 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310308780883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_30 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83040098488363 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310312771929 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨30, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83040098488363 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310312771929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_31 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83005716991891 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155158367697 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨31, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83005716991891 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155158367697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_32 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (663770876857 / 800000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (577580183039 / 25000000000000 : ℝ))
      (E := (cell12258 ⟨32, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (663770876857 / 800000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (577580183039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_33 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (16587405260491 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310324764421 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨33, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (16587405260491 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310324764421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_34 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (16580543409287 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310328717039 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨34, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (16580543409287 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310328717039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_35 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (82868431807777 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310332708787 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨35, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (82868431807777 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310332708787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_36 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41417085277677 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (36099011581 / 1562500000000 : ℝ))
      (E := (cell12258 ⟨36, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41417085277677 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (36099011581 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_37 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (82799933258197 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155170349129 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨37, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (82799933258197 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155170349129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_38 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (16553143977099 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (288793087281 / 12500000000000 : ℝ))
      (E := (cell12258 ⟨38, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (16553143977099 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (288793087281 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_39 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (1292680162603 / 1562500000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310348683317 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨39, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (1292680162603 / 1562500000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310348683317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12259_20 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (20846309274831 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (92405051631 / 4000000000000 : ℝ))
      (E := (cell12259 ⟨20, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (20846309274831 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (92405051631 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_21 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (20837653259929 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310130278337 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨21, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (20837653259929 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310130278337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_22 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83316013416547 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310134265259 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨22, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83316013416547 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310134265259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_23 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83281438196537 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310138256089 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨23, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83281438196537 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310138256089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_24 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (4162344367329 / 5000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310142255137 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨24, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (4162344367329 / 5000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310142255137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_25 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83212360833739 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (92405850659 / 4000000000000 : ℝ))
      (E := (cell12259 ⟨25, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83212360833739 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (92405850659 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_26 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (2599308082039 / 3125000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462030047113 / 20000000000000 : ℝ))
      (E := (cell12259 ⟨26, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (2599308082039 / 3125000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462030047113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_27 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (20785845172127 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (288769285341 / 12500000000000 : ℝ))
      (E := (cell12259 ⟨27, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (20785845172127 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (288769285341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_28 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83108926991089 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310158236139 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨28, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83108926991089 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310158236139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_29 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83074497500729 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (231016221567 / 10000000000000 : ℝ))
      (E := (cell12259 ⟨29, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83074497500729 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (231016221567 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_30 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83040092185327 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310166224223 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨30, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83040092185327 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310166224223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_31 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (1660114220259 / 2000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310170205969 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨31, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (1660114220259 / 2000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310170205969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_32 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82971353951827 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155087110893 / 50000000000000 : ℝ))
      (E := (cell12259 ⟨32, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82971353951827 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155087110893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_33 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82937020970351 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310178215339 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨33, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82937020970351 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310178215339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_34 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (3316108481483 / 4000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310182188533 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨34, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (3316108481483 / 4000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310182188533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_35 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82868427120713 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155093100813 / 50000000000000 : ℝ))
      (E := (cell12259 ⟨35, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82868427120713 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155093100813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_36 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82834166190139 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (231019019753 / 10000000000000 : ℝ))
      (E := (cell12259 ⟨36, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82834166190139 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (231019019753 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_37 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (82799929214383 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310194177467 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨37, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (82799929214383 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310194177467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_38 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (20691429040659 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310198201087 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨38, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (20691429040659 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310198201087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_39 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (20682881751061 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155101105277 / 50000000000000 : ℝ))
      (E := (cell12259 ⟨39, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (20682881751061 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155101105277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12260_20 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (5211576720759 / 6250000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309979889673 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨20, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (5211576720759 / 6250000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309979889673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_21 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (1667012076023 / 2000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154991914819 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨21, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (1667012076023 / 2000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154991914819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_22 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (16663200901227 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309987827977 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨22, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (16663200901227 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309987827977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_23 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83281429613819 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309991831007 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨23, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83281429613819 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309991831007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_24 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41623439545549 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154997921517 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨24, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41623439545549 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154997921517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_25 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (20803088226259 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154999904891 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨25, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (20803088226259 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154999904891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_26 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83177851022867 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (462000758677 / 20000000000000 : ℝ))
      (E := (cell12260 ⟨26, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83177851022867 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (462000758677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_27 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (16628674682399 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155003898721 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨27, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (16628674682399 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155003898721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_28 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83108920039989 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310011825317 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨28, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83108920039989 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310011825317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_29 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83074490874587 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310015821693 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨29, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83074490874587 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310015821693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_30 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83040085883691 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155009894699 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨30, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83040085883691 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155009894699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_31 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83005705035369 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (288752973689 / 12500000000000 : ℝ))
      (E := (cell12260 ⟨31, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83005705035369 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (288752973689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_32 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (1659426965957 / 2000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155013882979 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨32, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (1659426965957 / 2000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1155013882979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_33 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (82937015639527 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310031779403 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨33, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (82937015639527 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310031779403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_34 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (16580541405791 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (115501788663 / 5000000000000 : ℝ))
      (E := (cell12260 ⟨34, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (16580541405791 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (115501788663 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_35 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (2589638201089 / 3125000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577509937301 / 25000000000000 : ℝ))
      (E := (cell12260 ⟨35, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (2589638201089 / 3125000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (577509937301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_36 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (82834161826081 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310043767289 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨36, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (82834161826081 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310043767289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_37 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41399962585843 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310047770177 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨37, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41399962585843 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310047770177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_38 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41382856220427 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310051758861 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨38, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41382856220427 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2310051758861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_39 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (20682880900733 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (72189241691 / 3125000000000 : ℝ))
      (E := (cell12260 ⟨39, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (20682880900733 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (72189241691 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12261_20 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (10423152245847 / 12500000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (36091148189 / 1562500000000 : ℝ))
      (E := (cell12261 ⟨20, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (10423152245847 / 12500000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (36091148189 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_21 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (16670118912871 / 20000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154918746509 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨21, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (16670118912871 / 20000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154918746509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_22 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83315995597451 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461968300573 / 20000000000000 : ℝ))
      (E := (cell12261 ⟨22, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83315995597451 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461968300573 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_23 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83281421032789 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (57746136497 / 2500000000000 : ℝ))
      (E := (cell12261 ⟨23, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83281421032789 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (57746136497 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_24 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83246870837263 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288731185619 / 12500000000000 : ℝ))
      (E := (cell12261 ⟨24, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83246870837263 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288731185619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_25 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83212344977939 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577463366381 / 25000000000000 : ℝ))
      (E := (cell12261 ⟨25, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83212344977939 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577463366381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_26 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (20794460855513 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (230985746373 / 10000000000000 : ℝ))
      (E := (cell12261 ⟨26, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (20794460855513 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (230985746373 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_27 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (16628673227401 / 20000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (72183171349 / 3125000000000 : ℝ))
      (E := (cell12261 ⟨27, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (16628673227401 / 20000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (72183171349 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_28 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83108913090371 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309865468779 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨28, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83108913090371 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309865468779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_29 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (2596077632809 / 3125000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309869423621 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨29, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (2596077632809 / 3125000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309869423621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_30 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83040079583457 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309873467453 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨30, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83040079583457 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309873467453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_31 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (20751424764787 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (144367339221 / 6250000000000 : ℝ))
      (E := (cell12261 ⟨31, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (20751424764787 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (144367339221 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_32 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (10371417830649 / 12500000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309881423189 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨32, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (10371417830649 / 12500000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309881423189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_33 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82937010309981 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154942699039 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨33, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82937010309981 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154942699039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_34 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (10362837752759 / 12500000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288736176583 / 12500000000000 : ℝ))
      (E := (cell12261 ⟨34, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (10362837752759 / 12500000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288736176583 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_35 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (4143420887509 / 5000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577473352527 / 25000000000000 : ℝ))
      (E := (cell12261 ⟨35, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (4143420887509 / 5000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577473352527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_36 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82834157463181 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154948695927 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨36, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82834157463181 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154948695927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_37 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (41399960565053 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154950708879 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨37, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (41399960565053 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154950708879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_38 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82765708720149 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (230990537157 / 10000000000000 : ℝ))
      (E := (cell12261 ⟨38, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82765708720149 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (230990537157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_39 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (82731520202657 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309909371349 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨39, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (82731520202657 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309909371349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12262_20 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (4169260420161 / 5000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154843624371 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨20, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (4169260420161 / 5000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154843624371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_21 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83350585329329 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (144355700639 / 6250000000000 : ℝ))
      (E := (cell12262 ⟨21, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83350585329329 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (144355700639 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_22 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (1301812292039 / 1562500000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577423807911 / 25000000000000 : ℝ))
      (E := (cell12262 ⟨22, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (1301812292039 / 1562500000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577423807911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_23 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41640706226723 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309699201013 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨23, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41640706226723 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309699201013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_24 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41623431292537 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309703180893 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨24, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41623431292537 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309703180893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_25 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83212337052447 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (461941435071 / 20000000000000 : ℝ))
      (E := (cell12262 ⟨25, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83212337052447 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (461941435071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_26 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (207944589557 / 250000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (230971118823 / 10000000000000 : ℝ))
      (E := (cell12262 ⟨26, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (207944589557 / 250000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (230971118823 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_27 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83143358863539 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309715164717 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨27, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83143358863539 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309715164717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_28 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (20777226535559 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309719166527 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨28, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (20777226535559 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309719166527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_29 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83074477626629 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577430799197 / 25000000000000 : ℝ))
      (E := (cell12262 ⟨29, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83074477626629 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577430799197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_30 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (5190004580289 / 6250000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (92389087997 / 4000000000000 : ℝ))
      (E := (cell12262 ⟨30, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (5190004580289 / 6250000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (92389087997 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_31 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83005693084287 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309731178533 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨31, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83005693084287 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309731178533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_32 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82971336993853 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (288716891871 / 12500000000000 : ℝ))
      (E := (cell12262 ⟨32, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82971336993853 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (288716891871 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_33 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41468502490857 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309739129903 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨33, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41468502490857 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309739129903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_34 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (20725674254107 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309743165307 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨34, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (20725674254107 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309743165307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_35 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (8286841306671 / 10000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154873562877 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨35, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (8286841306671 / 10000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154873562877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_36 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82834153101437 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577437782459 / 25000000000000 : ℝ))
      (E := (cell12262 ⟨36, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82834153101437 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577437782459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_37 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (20699979272411 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (230975512021 / 10000000000000 : ℝ))
      (E := (cell12262 ⟨37, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (20699979272411 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (230975512021 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_38 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82765705000521 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309759097871 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨38, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82765705000521 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309759097871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_39 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (82731516803417 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577440780567 / 25000000000000 : ℝ))
      (E := (cell12262 ⟨39, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (82731516803417 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577440780567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12263_20 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41692599420737 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309541067149 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨20, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41692599420737 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309541067149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_21 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (10418822012009 / 12500000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288693129939 / 12500000000000 : ℝ))
      (E := (cell12263 ⟨21, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (10418822012009 / 12500000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288693129939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_22 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (8331597778527 / 10000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154774507157 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨22, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (8331597778527 / 10000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154774507157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_23 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (8328140387579 / 10000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309553054407 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨23, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (8328140387579 / 10000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309553054407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_24 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83246854334531 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309557047511 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨24, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83246854334531 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309557047511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_25 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83212329128559 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154780498813 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨25, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83212329128559 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154780498813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_26 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (10397228528139 / 12500000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154782512629 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨26, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (10397228528139 / 12500000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154782512629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_27 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (20785837897899 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309569017279 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨27, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (20785837897899 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309569017279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_28 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41554449597791 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309572976981 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨28, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41554449597791 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309572976981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_29 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (20768617751203 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154788482931 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨29, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (20768617751203 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154788482931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_30 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (8304006698719 / 10000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (461916197363 / 20000000000000 : ℝ))
      (E := (cell12263 ⟨30, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (8304006698719 / 10000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (461916197363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_31 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41502843555393 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309584984011 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨31, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41502843555393 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309584984011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_32 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (82971331343833 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (230958895981 / 10000000000000 : ℝ))
      (E := (cell12263 ⟨32, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (82971331343833 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (230958895981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_33 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (3317479986189 / 4000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309592974879 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨33, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (3317479986189 / 4000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309592974879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_34 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (82902692012021 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577399243157 / 25000000000000 : ℝ))
      (E := (cell12263 ⟨34, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (82902692012021 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577399243157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_35 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41434204192219 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288700119341 / 12500000000000 : ℝ))
      (E := (cell12263 ⟨35, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41434204192219 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288700119341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_36 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (82834148740851 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (18476839381 / 800000000000 : ℝ))
      (E := (cell12263 ⟨36, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (82834148740851 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (18476839381 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_37 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (82799913050297 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309608936169 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨37, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (82799913050297 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309608936169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_38 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (5172856330123 / 6250000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288701617221 / 12500000000000 : ℝ))
      (E := (cell12263 ⟨38, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (5172856330123 / 6250000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288701617221 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_39 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41365756702607 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (230961692819 / 10000000000000 : ℝ))
      (E := (cell12263 ⟨39, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41365756702607 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (230961692819 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12264_20 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41692594640769 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154697469659 / 50000000000000 : ℝ))
      (E := (cell12264 ⟨20, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41692594640769 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154697469659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_21 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (16670113372917 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309398922627 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨21, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (16670113372917 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309398922627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_22 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83315968881771 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309402909159 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨22, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83315968881771 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309402909159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_23 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83281395299821 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309406903457 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨23, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83281395299821 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309406903457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_24 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83246846085633 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577352727457 / 25000000000000 : ℝ))
      (E := (cell12264 ⟨24, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83246846085633 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577352727457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_25 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (20803080301569 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309414932337 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨25, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (20803080301569 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309414932337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_26 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (20794455157247 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154709458221 / 50000000000000 : ℝ))
      (E := (cell12264 ⟨26, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (20794455157247 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154709458221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_27 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41571672160587 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154711462033 / 50000000000000 : ℝ))
      (E := (cell12264 ⟨27, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41571672160587 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154711462033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_28 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (8310889225041 / 10000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (144339181259 / 6250000000000 : ℝ))
      (E := (cell12264 ⟨28, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (8310889225041 / 10000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (144339181259 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_29 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (16614892876887 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154715453089 / 50000000000000 : ℝ))
      (E := (cell12264 ⟨29, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (16614892876887 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154715453089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_30 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (20760015172789 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (36084920103 / 1562500000000 : ℝ))
      (E := (cell12264 ⟨30, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (20760015172789 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (36084920103 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_31 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (20751420284661 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (461887780493 / 20000000000000 : ℝ))
      (E := (cell12264 ⟨31, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (20751420284661 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (461887780493 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_32 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82971325695131 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577360724429 / 25000000000000 : ℝ))
      (E := (cell12264 ⟨32, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82971325695131 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577360724429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_33 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41468497164507 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309446874471 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨33, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41468497164507 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309446874471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_34 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (20725671752213 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309450834629 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨34, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (20725671752213 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309450834629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_35 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41434201851681 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (144340927403 / 6250000000000 : ℝ))
      (E := (cell12264 ⟨35, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41434201851681 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (144340927403 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_36 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82834144381421 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154729414417 / 50000000000000 : ℝ))
      (E := (cell12264 ⟨36, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82834144381421 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154729414417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_37 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41399954506033 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577365716409 / 25000000000000 : ℝ))
      (E := (cell12264 ⟨37, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41399954506033 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577365716409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_38 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (82765697564491 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (461893366521 / 20000000000000 : ℝ))
      (E := (cell12264 ⟨38, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (82765697564491 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (461893366521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_39 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41365755004023 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309470847797 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨39, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41365755004023 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309470847797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12265_20 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83385179723413 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154624461741 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨20, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83385179723413 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154624461741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_21 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41675278817433 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577313229457 / 25000000000000 : ℝ))
      (E := (cell12265 ⟨21, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41675278817433 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577313229457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_22 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83315959979999 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154628458089 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨22, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83315959979999 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154628458089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_23 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41640693362769 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154630461537 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨23, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41640693362769 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154630461537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_24 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (4162341891919 / 5000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154632442249 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨24, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (4162341891919 / 5000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154632442249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_25 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83212313285597 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309268921141 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨25, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83212313285597 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309268921141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_26 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41588906517213 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154636430893 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨26, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41588906517213 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154636430893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_27 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (3325733482091 / 4000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (92371075403 / 4000000000000 : ℝ))
      (E := (cell12265 ⟨27, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (3325733482091 / 4000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (92371075403 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_28 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83108885306719 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577320219399 / 25000000000000 : ℝ))
      (E := (cell12265 ⟨28, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83108885306719 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577320219399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_29 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83074457765499 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577321210601 / 25000000000000 : ℝ))
      (E := (cell12265 ⟨29, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83074457765499 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577321210601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_30 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41520027198261 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309288840787 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨30, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41520027198261 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309288840787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_31 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (4150283758393 / 5000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (461858575081 / 20000000000000 : ℝ))
      (E := (cell12265 ⟨31, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (4150283758393 / 5000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (461858575081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_32 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82971320047747 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154648415829 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨32, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82971320047747 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154648415829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_33 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82936989004581 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309300828677 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨33, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82936989004581 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309300828677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_34 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82902682006919 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (461860973687 / 20000000000000 : ℝ))
      (E := (cell12265 ⟨34, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82902682006919 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (461860973687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_35 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41434199511741 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309308835499 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨35, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41434199511741 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309308835499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_36 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82834140023147 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154656424231 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨36, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82834140023147 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154656424231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_37 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82799904974951 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309316849979 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨37, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82799904974951 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309316849979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_38 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (8276569384809 / 10000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154660420519 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨38, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (8276569384809 / 10000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154660420519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_39 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (82731506611913 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (230932482241 / 10000000000000 : ℝ))
      (E := (cell12265 ⟨39, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (82731506611913 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (230932482241 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12266_20 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83385170167097 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577275754911 / 25000000000000 : ℝ))
      (E := (cell12266 ⟨20, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83385170167097 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577275754911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_21 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (20837637101729 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309106966859 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨21, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (20837637101729 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309106966859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_22 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41657975539977 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154555488547 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨22, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41657975539977 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154555488547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_23 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (4164068907647 / 5000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461822999331 / 20000000000000 : ℝ))
      (E := (cell12266 ⟨23, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (4164068907647 / 5000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461822999331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_24 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (20811707398193 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154559485761 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨24, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (20811707398193 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154559485761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_25 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83212305366521 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (57728074101 / 2500000000000 : ℝ))
      (E := (cell12266 ⟨25, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83212305366521 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (57728074101 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_26 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83177805441427 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577281744509 / 25000000000000 : ℝ))
      (E := (cell12266 ⟨26, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83177805441427 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577281744509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_27 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83143329784897 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309130958707 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨27, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83143329784897 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309130958707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_28 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (20777219591127 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309134909339 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨28, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (20777219591127 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309134909339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_29 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41537225574001 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (18473111599 / 800000000000 : ℝ))
      (E := (cell12266 ⟨29, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41537225574001 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (18473111599 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_30 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83040048103287 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309142907873 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨30, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83040048103287 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309142907873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_31 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (16601133839687 / 20000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (144321681427 / 6250000000000 : ℝ))
      (E := (cell12266 ⟨31, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (16601133839687 / 20000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (144321681427 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_32 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (82971314401681 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309150937181 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨32, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (82971314401681 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309150937181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_33 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (5183561480089 / 6250000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (57728872401 / 2500000000000 : ℝ))
      (E := (cell12266 ⟨33, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (5183561480089 / 6250000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (57728872401 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_34 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (82902677006223 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154579449181 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨34, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (82902677006223 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154579449181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_35 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41434197172399 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309162887299 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨35, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41434197172399 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309162887299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_36 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (82834135666029 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461833372859 / 20000000000000 : ℝ))
      (E := (cell12266 ⟨36, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (82834135666029 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (461833372859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_37 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (10349987617369 / 12500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309170889199 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨37, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (10349987617369 / 12500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309170889199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_38 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (20691422533191 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154587452207 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨38, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (20691422533191 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154587452207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_39 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (5170718951051 / 6250000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309178852029 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨39, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (5170718951051 / 6250000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309178852029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12267_20 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83385160612589 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154478555671 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨20, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83385160612589 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154478555671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_21 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83350539180733 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308961127981 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨21, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83350539180733 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308961127981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_22 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (20828985545409 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577241287547 / 25000000000000 : ℝ))
      (E := (cell12267 ⟨22, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (20828985545409 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577241287547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_23 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (20820342395507 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308969124201 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨23, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (20820342395507 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308969124201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_24 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (10405852668601 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308973112579 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨24, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (10405852668601 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308973112579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_25 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (10401537181131 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154488559693 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨25, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (10401537181131 / 12500000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154488559693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_26 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83177797849989 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577245272519 / 25000000000000 : ℝ))
      (E := (cell12267 ⟨26, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83177797849989 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577245272519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_27 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (32477860359 / 39062500000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308985086567 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨27, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (32477860359 / 39062500000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308985086567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_28 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (41554435711889 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308989112217 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨28, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (41554435711889 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308989112217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_29 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (16614888906389 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308993053261 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨29, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (16614888906389 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308993053261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_30 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (1660800836229 / 2000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308997087851 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨30, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (1660800836229 / 2000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308997087851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_31 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (2593926975949 / 3125000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309001043239 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨31, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (2593926975949 / 3125000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309001043239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_32 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82971308756933 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288625629843 / 12500000000000 : ℝ))
      (E := (cell12267 ⟨32, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82971308756933 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288625629843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_33 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (16587395671909 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309009076561 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨33, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (16587395671909 / 20000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309009076561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_34 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (20725668001691 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461802608307 / 20000000000000 : ℝ))
      (E := (cell12267 ⟨34, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (20725668001691 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461802608307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_35 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82868389667311 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154508526217 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨35, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82868389667311 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154508526217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_36 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (41417065655033 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309021052161 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨36, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (41417065655033 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309021052161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_37 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (82799896904067 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309025041933 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨37, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (82799896904067 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309025041933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_38 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (5172855401157 / 6250000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (144314313921 / 6250000000000 : ℝ))
      (E := (cell12267 ⟨38, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (5172855401157 / 6250000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (144314313921 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_39 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (2585359369461 / 3125000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309033054019 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨39, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (2585359369461 / 3125000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2309033054019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12268_20 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (83385151059891 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308811373271 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨20, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (83385151059891 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308811373271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_21 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (83350529956317 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (288601917867 / 12500000000000 : ℝ))
      (E := (cell12268 ⟨21, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (83350529956317 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (288601917867 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_22 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (20828983321261 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154409688591 / 50000000000000 : ℝ))
      (E := (cell12268 ⟨22, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (20828983321261 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154409688591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_23 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (52050850633 / 62500000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461764672803 / 20000000000000 : ℝ))
      (E := (cell12268 ⟨23, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (52050850633 / 62500000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461764672803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_24 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (10405851638311 / 12500000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (288603420749 / 12500000000000 : ℝ))
      (E := (cell12268 ⟨24, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (10405851638311 / 12500000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (288603420749 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_25 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41606144766589 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308831328827 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨25, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41606144766589 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308831328827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_26 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41588895130057 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308835314649 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨26, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41588895130057 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308835314649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_27 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (5196457203419 / 6250000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577209831763 / 25000000000000 : ℝ))
      (E := (cell12268 ⟨27, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (5196457203419 / 6250000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577209831763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_28 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (83108864484527 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (288605413871 / 12500000000000 : ℝ))
      (E := (cell12268 ⟨28, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (83108864484527 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (288605413871 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_29 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41537218958663 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461769465579 / 20000000000000 : ℝ))
      (E := (cell12268 ⟨29, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41537218958663 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461769465579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_30 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (20760008880253 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577212830563 / 25000000000000 : ℝ))
      (E := (cell12268 ⟨30, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (20760008880253 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577212830563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_31 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41502828631829 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577213824157 / 25000000000000 : ℝ))
      (E := (cell12268 ⟨31, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41502828631829 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577213824157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_32 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82971303113501 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577214827973 / 25000000000000 : ℝ))
      (E := (cell12268 ⟨32, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82971303113501 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577214827973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_33 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82936973038941 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308863311703 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨33, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82936973038941 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308863311703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_34 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (4145133350427 / 5000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461773459591 / 20000000000000 : ℝ))
      (E := (cell12268 ⟨34, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (4145133350427 / 5000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461773459591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_35 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41434192495509 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308871272319 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨35, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41434192495509 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308871272319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_36 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41417063477629 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154437647421 / 50000000000000 : ℝ))
      (E := (cell12268 ⟨36, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41417063477629 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154437647421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_37 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41399946435149 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461775849909 / 20000000000000 : ℝ))
      (E := (cell12268 ⟨37, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41399946435149 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461775849909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_38 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (16553136541067 / 20000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308883254659 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨38, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (16553136541067 / 20000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308883254659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_39 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (82731496429723 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154443626169 / 50000000000000 : ℝ))
      (E := (cell12268 ⟨39, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (82731496429723 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154443626169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12269_20 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83385141509 / 100000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577166422243 / 25000000000000 : ℝ))
      (E := (cell12269 ⟨20, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83385141509 / 100000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577166422243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_21 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (20837630183417 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (72145927187 / 3125000000000 : ℝ))
      (E := (cell12269 ⟨21, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (20837630183417 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (72145927187 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_22 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83315924390177 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154336829039 / 50000000000000 : ℝ))
      (E := (cell12269 ⟨22, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83315924390177 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154336829039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_23 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83281352445257 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308677657797 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨23, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83281352445257 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308677657797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_24 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (8324680486581 / 10000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (14429260459 / 625000000000 : ℝ))
      (E := (cell12269 ⟨24, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (8324680486581 / 10000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (14429260459 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_25 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (8321228161891 / 10000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308685650719 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨25, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (8321228161891 / 10000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308685650719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_26 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83177782671799 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577172412941 / 25000000000000 : ℝ))
      (E := (cell12269 ⟨26, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83177782671799 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577172412941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_27 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (5196456749493 / 6250000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288586702721 / 12500000000000 : ℝ))
      (E := (cell12269 ⟨27, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (5196456749493 / 6250000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288586702721 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_28 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (20777214386689 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461739524487 / 20000000000000 : ℝ))
      (E := (cell12269 ⟨28, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (20777214386689 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461739524487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_29 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83074431304147 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461740319689 / 20000000000000 : ℝ))
      (E := (cell12269 ⟨29, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83074431304147 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461740319689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_30 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (20760007307993 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308705611081 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨30, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (20760007307993 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308705611081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_31 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (16601130259661 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308709604509 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨31, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (16601130259661 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308709604509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_32 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41485648735693 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308713581083 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨32, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41485648735693 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308713581083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_33 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41468483859807 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308717601467 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨33, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41468483859807 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308717601467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_34 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (2590708187861 / 3125000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288590201133 / 12500000000000 : ℝ))
      (E := (cell12269 ⟨34, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (2590708187861 / 3125000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288590201133 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_35 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (82868380315921 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154362802771 / 50000000000000 : ℝ))
      (E := (cell12269 ⟨35, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (82868380315921 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154362802771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_36 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (16566824520321 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308729592341 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨36, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (16566824520321 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308729592341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_37 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41399944418821 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154366785337 / 50000000000000 : ℝ))
      (E := (cell12269 ⟨37, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41399944418821 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154366785337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_38 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (5172854937077 / 6250000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461747520037 / 20000000000000 : ℝ))
      (E := (cell12269 ⟨38, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (5172854937077 / 6250000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461747520037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_39 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (2585359157429 / 3125000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (46174831287 / 2000000000000 : ℝ))
      (E := (cell12269 ⟨39, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (2585359157429 / 3125000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (46174831287 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12270_20 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83385131959917 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308520058443 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨20, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83385131959917 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308520058443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_21 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (16670102302557 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577131012717 / 25000000000000 : ℝ))
      (E := (cell12270 ⟨21, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (16670102302557 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577131012717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_22 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (16663183099407 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308528051157 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨22, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (16663183099407 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308528051157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_23 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83281343879397 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308532063851 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨23, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83281343879397 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308532063851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_24 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (10405849578347 / 12500000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308536034921 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨24, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (10405849578347 / 12500000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308536034921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_25 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (20803068426561 / 25000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (230854002671 / 10000000000000 : ℝ))
      (E := (cell12270 ⟨25, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (20803068426561 / 25000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (230854002671 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_26 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (41588887542523 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308544043043 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨26, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (41588887542523 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308544043043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_27 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (2598228147831 / 3125000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (288568503639 / 12500000000000 : ℝ))
      (E := (cell12270 ⟨27, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (2598228147831 / 3125000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (288568503639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_28 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83108850610463 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308552046621 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨28, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83108850610463 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308552046621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_29 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (16614884938481 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308556040247 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨29, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (16614884938481 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308556040247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_30 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83040022944329 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461712002561 / 20000000000000 : ℝ))
      (E := (cell12270 ⟨30, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83040022944329 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461712002561 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_31 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83005645334309 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154282012687 / 50000000000000 : ℝ))
      (E := (cell12270 ⟨31, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83005645334309 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154282012687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_32 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82971291830587 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154284010931 / 50000000000000 : ℝ))
      (E := (cell12270 ⟨32, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82971291830587 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154284010931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_33 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (41468481200781 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308572004393 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨33, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (41468481200781 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308572004393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_34 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (41451328507899 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308575974861 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨34, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (41451328507899 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308575974861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_35 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82868375642019 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308579993519 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨35, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82868375642019 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308579993519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_36 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (41417059124553 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308584003267 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨36, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (41417059124553 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308584003267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_37 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82799884806101 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154293973343 / 50000000000000 : ℝ))
      (E := (cell12270 ⟨37, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82799884806101 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154293973343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_38 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82765675282203 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308591942003 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨38, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82765675282203 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308591942003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_39 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (82731489646767 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154297995027 / 50000000000000 : ℝ))
      (E := (cell12270 ⟨39, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (82731489646767 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (1154297995027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12271_20 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (521157015079 / 625000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154187269961 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨20, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (521157015079 / 625000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154187269961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_21 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (20837625573417 / 25000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308378543849 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨21, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (20837625573417 / 25000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308378543849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_22 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83315906605617 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308382556423 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨22, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83315906605617 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308382556423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_23 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83281335315221 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308386523877 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨23, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83281335315221 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308386523877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_24 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83246788389383 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308390508767 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨24, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83246788389383 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308390508767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_25 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83212265795179 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461678903031 / 20000000000000 : ℝ))
      (E := (cell12271 ⟨25, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83212265795179 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461678903031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_26 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (20794441874963 / 25000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308398488491 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨26, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (20794441874963 / 25000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308398488491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_27 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (2598227920963 / 3125000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308402490689 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨27, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (2598227920963 / 3125000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308402490689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_28 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (1662176873513 / 2000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461681305021 / 20000000000000 : ℝ))
      (E := (cell12271 ⟨28, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (1662176873513 / 2000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461681305021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_29 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83074418082101 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (144275654873 / 6250000000000 : ℝ))
      (E := (cell12271 ⟨29, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83074418082101 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (144275654873 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_30 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83040016658083 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308414468959 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨30, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83040016658083 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308414468959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_31 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (8300563937167 / 10000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154209250367 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨31, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (8300563937167 / 10000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154209250367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_32 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (81026646671 / 97656250000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461684491737 / 20000000000000 : ℝ))
      (E := (cell12271 ⟨32, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (81026646671 / 97656250000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461684491737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_33 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (41468478542393 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288553307743 / 12500000000000 : ℝ))
      (E := (cell12271 ⟨33, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (41468478542393 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288553307743 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_34 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (518141575133 / 625000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308430453911 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨34, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (518141575133 / 625000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308430453911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_35 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82868370969311 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308434436251 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨35, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82868370969311 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308434436251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_36 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82834113897761 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461687693803 / 20000000000000 : ℝ))
      (E := (cell12271 ⟨36, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82834113897761 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461687693803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_37 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82799880775673 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288555304527 / 12500000000000 : ℝ))
      (E := (cell12271 ⟨37, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82799880775673 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288555304527 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_38 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82765671572247 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461689291217 / 20000000000000 : ℝ))
      (E := (cell12271 ⟨38, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82765671572247 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461689291217 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_39 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (82731486256839 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154225235387 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨39, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (82731486256839 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154225235387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12272_20 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83385112867171 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308229133407 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨20, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83385112867171 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308229133407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_21 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (20837623269079 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308233090669 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨21, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (20837623269079 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308233090669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_22 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (20828974428981 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308237115593 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨22, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (20828974428981 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308237115593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_23 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (10410165844091 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308241096177 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨23, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (10410165844091 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308241096177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_24 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83246780153633 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308245094977 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨24, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83246780153633 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308245094977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_25 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (16642451577143 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154124528851 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨25, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (16642451577143 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154124528851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_26 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83177759916219 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (28853163081 / 1250000000000 : ℝ))
      (E := (cell12272 ⟨26, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83177759916219 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (28853163081 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_27 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41571643106279 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308257064899 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨27, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41571643106279 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308257064899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_28 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41554418371157 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308261057889 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨28, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41554418371157 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308261057889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_29 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (16614882294647 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308265028499 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨29, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (16614882294647 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308265028499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_30 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83040010373233 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (577067259503 / 25000000000000 : ℝ))
      (E := (cell12272 ⟨30, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83040010373233 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (577067259503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_31 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83005633410387 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308273030589 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨31, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83005633410387 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308273030589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_32 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (10371410069117 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308277067101 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨32, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (10371410069117 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308277067101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_33 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (20734237942321 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (115414051633 / 5000000000000 : ℝ))
      (E := (cell12272 ⟨33, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (20734237942321 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (115414051633 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_34 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (20725661756999 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308285046213 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨34, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (20725661756999 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308285046213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_35 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82868366297797 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308289050911 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨35, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82868366297797 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308289050911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_36 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (8283410954757 / 10000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154146494791 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨36, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (8283410954757 / 10000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154146494791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_37 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82799876746359 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (461659407853 / 20000000000000 : ℝ))
      (E := (cell12272 ⟨37, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82799876746359 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (461659407853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_38 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (16553133572673 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308301025117 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨38, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (16553133572673 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308301025117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_39 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (82731482867943 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (230830500651 / 10000000000000 : ℝ))
      (E := (cell12272 ⟨39, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (82731482867943 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (230830500651 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12273_20 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83385103323507 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308083780669 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨20, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83385103323507 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308083780669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_21 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83350483860729 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308087749589 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨21, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83350483860729 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308087749589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_22 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41657944413977 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308091728671 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨22, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41657944413977 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308091728671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_23 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83281318191917 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308095722451 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨23, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83281318191917 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308095722451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_24 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (20811692979881 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308099735227 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨24, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (20811692979881 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308099735227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_25 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83212249977851 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154051856353 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨25, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83212249977851 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154051856353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_26 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (16635550466829 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461621543403 / 20000000000000 : ℝ))
      (E := (cell12273 ⟨26, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (16635550466829 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461621543403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_27 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83143278955819 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461622338669 / 20000000000000 : ℝ))
      (E := (cell12273 ⟨27, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83143278955819 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461622338669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_28 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83108829810457 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461623140679 / 20000000000000 : ℝ))
      (E := (cell12273 ⟨28, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83108829810457 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461623140679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_29 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41537202432903 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308119691841 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨29, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41537202432903 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308119691841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_30 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (4152000204489 / 5000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461624743993 / 20000000000000 : ℝ))
      (E := (cell12273 ⟨30, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (4152000204489 / 5000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461624743993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_31 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83005627450459 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461625534687 / 20000000000000 : ℝ))
      (E := (cell12273 ⟨31, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83005627450459 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461625534687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_32 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82971274916083 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577032917891 / 25000000000000 : ℝ))
      (E := (cell12273 ⟨32, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82971274916083 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577032917891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_33 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82936946455057 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577033914501 / 25000000000000 : ℝ))
      (E := (cell12273 ⟨33, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82936946455057 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577033914501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_34 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41451321017973 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (230813969321 / 10000000000000 : ℝ))
      (E := (cell12273 ⟨34, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41451321017973 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (230813969321 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_35 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (20717090406869 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (144258978859 / 6250000000000 : ℝ))
      (E := (cell12273 ⟨35, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (20717090406869 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (144258978859 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_36 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (20708526299633 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308147682193 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨36, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (20708526299633 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308147682193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_37 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41399936359079 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (230815163857 / 10000000000000 : ℝ))
      (E := (cell12273 ⟨37, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41399936359079 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (230815163857 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_38 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (16553132831111 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308155649103 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨38, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (16553132831111 / 20000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308155649103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_39 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (82731479480081 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154079827971 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨39, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (82731479480081 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154079827971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12274_20 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83385093781649 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307938481709 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨20, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83385093781649 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307938481709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_21 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (41675237323453 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307942462353 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨21, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (41675237323453 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307942462353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_22 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (20828969985427 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (115397322697 / 5000000000000 : ℝ))
      (E := (cell12274 ⟨22, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (20828969985427 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (115397322697 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_23 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83281309632789 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461590092201 / 20000000000000 : ℝ))
      (E := (cell12274 ⟨23, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83281309632789 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461590092201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_24 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (5202922730441 / 6250000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153977214759 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨24, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (5202922730441 / 6250000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153977214759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_25 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (20803060517897 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (288494802727 / 12500000000000 : ℝ))
      (E := (cell12274 ⟨25, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (20803060517897 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (288494802727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_26 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (8317774475363 / 10000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307962441723 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨26, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (8317774475363 / 10000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307962441723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_27 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (41571635850299 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307966434427 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨27, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (41571635850299 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307966434427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_28 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (20777205720019 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153985201603 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨28, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (20777205720019 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153985201603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_29 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83074398259813 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153987204777 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨29, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83074398259813 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153987204777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_30 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83039997807723 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461595679577 / 20000000000000 : ℝ))
      (E := (cell12274 ⟨30, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83039997807723 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461595679577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_31 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83005621491887 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (288497803659 / 12500000000000 : ℝ))
      (E := (cell12274 ⟨31, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83005621491887 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (288497803659 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_32 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (16594253856109 / 20000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307986389107 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨32, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (16594253856109 / 20000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307986389107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_33 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (16587388228421 / 20000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (576997599129 / 25000000000000 : ℝ))
      (E := (cell12274 ⟨33, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (16587388228421 / 20000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (576997599129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_34 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (8290263704513 / 10000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307994394901 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨34, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (8290263704513 / 10000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307994394901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_35 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82868356958349 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307998385923 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨35, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82868356958349 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307998385923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_36 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (10354262606331 / 12500000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1154001185509 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨36, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (10354262606331 / 12500000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1154001185509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_37 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (8279986869107 / 10000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308006351397 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨37, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (8279986869107 / 10000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308006351397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_38 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (41382830224409 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308010386699 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨38, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (41382830224409 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2308010386699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_39 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (82731476093251 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461602872079 / 20000000000000 : ℝ))
      (E := (cell12274 ⟨39, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (82731476093251 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461602872079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

end BstLean.Part263
