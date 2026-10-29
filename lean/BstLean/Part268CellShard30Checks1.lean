import BstLean.Part268CellShard30Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13100_20 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (20844255298669 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220477106819 / 10000000000000 : ℝ))
      (E := (cell13100 ⟨20, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (20844255298669 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220477106819 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_21 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41671310975619 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204775083183 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨21, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41671310975619 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204775083183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_22 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41654123415457 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102389551051 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨22, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41654123415457 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102389551051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_23 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (2602309243783 / 3125000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204783128261 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨23, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (2602309243783 / 3125000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204783128261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_24 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (83239568829183 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204787164737 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨24, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (83239568829183 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204787164737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_25 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (83205265882979 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102395577971 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨25, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (83205265882979 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102395577971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_26 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (16634197386059 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102397581437 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨26, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (16634197386059 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102397581437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_27 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (83136731939147 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220479918791 / 10000000000000 : ℝ))
      (E := (cell13100 ⟨27, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (83136731939147 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220479918791 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_28 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (5193906304857 / 6250000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102401587349 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨28, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (5193906304857 / 6250000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102401587349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_29 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (83068293714331 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204807183611 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨29, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (83068293714331 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204807183611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_30 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41517055208753 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204811216339 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨30, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41517055208753 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204811216339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_31 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (829999509559 / 1000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204815215767 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨31, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (829999509559 / 1000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204815215767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_32 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41482907649167 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102409620829 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨32, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41482907649167 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102409620829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_33 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (20732925853447 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204823236399 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨33, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (20732925853447 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204823236399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_34 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (82897615271401 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204827259343 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨34, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (82897615271401 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204827259343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_35 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41431775420233 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204831311049 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨35, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41431775420233 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204831311049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_36 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (82829510090433 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (551208818617 / 25000000000000 : ℝ))
      (E := (cell13100 ⟨36, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (82829510090433 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (551208818617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_37 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (82795492990907 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102419662857 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨37, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (82795492990907 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102419662857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_38 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41380749755823 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220484334727 / 10000000000000 : ℝ))
      (E := (cell13100 ⟨38, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41380749755823 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (220484334727 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_39 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (517047060141 / 625000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102423669367 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨39, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (517047060141 / 625000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102423669367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13101_20 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (5211062943913 / 6250000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551164771317 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨20, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (5211062943913 / 6250000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551164771317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_21 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83342607865371 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551165774233 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨21, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83342607865371 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551165774233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_22 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83308232751243 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (220466711257 / 10000000000000 : ℝ))
      (E := (cell13101 ⟨22, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83308232751243 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (220466711257 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_23 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (10409235215947 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102335538553 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨23, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (10409235215947 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102335538553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_24 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83239554761887 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204675110371 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨24, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83239554761887 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204675110371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_25 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83205251821863 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551169789211 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨25, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83205251821863 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551169789211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_26 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (41585486437677 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (55117079017 / 2500000000000 : ℝ))
      (E := (cell13101 ⟨26, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (41585486437677 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (55117079017 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_27 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (665093743123 / 800000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551171795667 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨27, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (665093743123 / 800000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551171795667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_28 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (2596952713597 / 3125000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204691166453 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨28, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (2596952713597 / 3125000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204691166453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_29 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (41534139838941 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204695172409 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨29, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (41534139838941 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204695172409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_30 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (83034096387211 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204699202227 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨30, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (83034096387211 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204699202227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_31 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82999936931753 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204703198793 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨31, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82999936931753 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204703198793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_32 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (8296580128033 / 10000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204707221867 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨32, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (8296580128033 / 10000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204707221867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_33 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82931689401923 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551177803459 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨33, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82931689401923 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551177803459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_34 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82897601265669 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440943046811 / 20000000000000 : ℝ))
      (E := (cell13101 ⟨34, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82897601265669 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440943046811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_35 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (41431768420431 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204719283083 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨35, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (41431768420431 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204719283083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_36 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (10353687012119 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204723302561 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨36, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (10353687012119 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204723302561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_37 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (10349434875443 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (220472729253 / 10000000000000 : ℝ))
      (E := (cell13101 ⟨37, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (10349434875443 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (220472729253 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_38 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (16552297106079 / 20000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204731311547 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨38, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (16552297106079 / 20000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204731311547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_39 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82727515647417 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204735300517 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨39, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82727515647417 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204735300517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13102_20 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41688496506347 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (275568387261 / 12500000000000 : ℝ))
      (E := (cell13102 ⟨20, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41688496506347 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (275568387261 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_21 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (83342593781657 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (88182044257 / 4000000000000 : ℝ))
      (E := (cell13102 ⟨21, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (83342593781657 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (88182044257 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_22 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (20827054668431 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204555118781 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨22, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (20827054668431 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204555118781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_23 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41636933828123 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551139770021 / 25000000000000 : ℝ))
      (E := (cell13102 ⟨23, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41636933828123 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551139770021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_24 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41619770348371 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204563110161 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨24, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41619770348371 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204563110161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_25 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (83205237762897 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204567153493 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨25, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (83205237762897 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204567153493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_26 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (83170958822561 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102285577117 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨26, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (83170958822561 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102285577117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_27 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (2660374523 / 3200000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102287586587 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨27, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (2660374523 / 3200000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102287586587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_28 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (83102472794643 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551144788489 / 25000000000000 : ℝ))
      (E := (cell13102 ⟨28, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (83102472794643 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551144788489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_29 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41534132821789 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204583156959 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨29, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41534132821789 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204583156959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_30 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (4151704117953 / 5000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204587183867 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨30, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (4151704117953 / 5000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204587183867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_31 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (331999691639 / 400000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (137786952259 / 6250000000000 : ℝ))
      (E := (cell13102 ⟨31, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (331999691639 / 400000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (137786952259 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_32 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (82965787264469 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551148799457 / 25000000000000 : ℝ))
      (E := (cell13102 ⟨32, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (82965787264469 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551148799457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_33 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (414658376961 / 500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204599245647 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨33, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (414658376961 / 500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204599245647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_34 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41448793631039 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102301631583 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨34, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41448793631039 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102301631583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_35 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41431761421699 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (275575906359 / 12500000000000 : ℝ))
      (E := (cell13102 ⟨35, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41431761421699 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (275575906359 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_36 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (8282948210561 / 10000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204611267719 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨36, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (8282948210561 / 10000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204611267719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_37 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41397732509159 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102307656909 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨37, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41397732509159 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102307656909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_38 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41380735775641 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204619330319 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨38, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41380735775641 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204619330319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_39 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (8272750167441 / 10000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204623316821 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨39, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (8272750167441 / 10000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204623316821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13103_20 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83376978924933 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204435106651 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨20, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83376978924933 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204435106651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_21 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (651113903907 / 781250000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204439111661 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨21, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (651113903907 / 781250000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204439111661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_22 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (20827051149589 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204443120739 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨22, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (20827051149589 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204443120739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_23 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83273853587067 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440889427439 / 20000000000000 : ℝ))
      (E := (cell13103 ⟨23, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83273853587067 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440889427439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_24 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41619763316873 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551112791027 / 25000000000000 : ℝ))
      (E := (cell13103 ⟨24, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41619763316873 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551112791027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_25 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83205223706079 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (220445514589 / 10000000000000 : ℝ))
      (E := (cell13103 ⟨25, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83205223706079 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (220445514589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_26 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (20792736192979 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204459143537 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨26, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (20792736192979 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204459143537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_27 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (10392086224909 / 12500000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (220446315943 / 10000000000000 : ℝ))
      (E := (cell13103 ⟨27, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (10392086224909 / 12500000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (220446315943 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_28 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83102458756327 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551116798929 / 25000000000000 : ℝ))
      (E := (cell13103 ⟨28, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83102458756327 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551116798929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_29 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (4153412580571 / 5000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102235597893 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨29, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (4153412580571 / 5000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102235597893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_30 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (83034068333053 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (220447521981 / 10000000000000 : ℝ))
      (E := (cell13103 ⟨30, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (83034068333053 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (220447521981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_31 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (82999908889889 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (88179168427 / 4000000000000 : ℝ))
      (E := (cell13103 ⟨31, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (82999908889889 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (88179168427 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_32 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (82965773250751 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (110224161407 / 5000000000000 : ℝ))
      (E := (cell13103 ⟨32, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (82965773250751 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (110224161407 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_33 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (82931661384617 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102243636607 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨33, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (82931661384617 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102243636607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_34 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41448786630313 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102245644017 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨34, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41448786630313 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102245644017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_35 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (82863508848073 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102247636543 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨35, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (82863508848073 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102247636543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_36 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41414734058203 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102249643663 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨36, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41414734058203 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102249643663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_37 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (8279545103523 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440900666173 / 20000000000000 : ℝ))
      (E := (cell13103 ⟨37, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (8279545103523 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440900666173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_38 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (2586295549197 / 3125000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551126836213 / 25000000000000 : ℝ))
      (E := (cell13103 ⟨38, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (2586295549197 / 3125000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551126836213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_39 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41363743851769 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440902265777 / 20000000000000 : ℝ))
      (E := (cell13103 ⟨39, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41363743851769 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440902265777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13104_20 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (41688482419663 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204323110959 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨20, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (41688482419663 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204323110959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_21 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (41671282810343 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (440865434197 / 20000000000000 : ℝ))
      (E := (cell13104 ⟨21, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (41671282810343 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (440865434197 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_22 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (4165409526257 / 5000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102165588403 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨22, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (4165409526257 / 5000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102165588403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_23 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (41636919760019 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204335190053 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨23, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (41636919760019 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204335190053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_24 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83239512572899 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551084803451 / 25000000000000 : ℝ))
      (E := (cell13104 ⟨24, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83239512572899 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551084803451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_25 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83205209651409 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204343192469 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨25, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83205209651409 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204343192469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_26 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (41585465361709 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204347187047 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨26, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (41585465361709 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204347187047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_27 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (83136675756941 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204351199917 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨27, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (83136675756941 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204351199917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_28 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (20775611180039 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204355233227 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨28, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (20775611180039 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204355233227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_29 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (16613647516281 / 20000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102179615183 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨29, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (16613647516281 / 20000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102179615183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_30 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (8303405430919 / 10000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102181625753 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨30, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (8303405430919 / 10000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102181625753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_31 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (20749973718043 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204367298107 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨31, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (20749973718043 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204367298107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_32 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82965759239173 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102185656403 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨32, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82965759239173 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102185656403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_33 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (3317265895167 / 4000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204375296537 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨33, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (3317265895167 / 4000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204375296537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_34 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (16579511852263 / 20000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102189654329 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨34, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (16579511852263 / 20000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102189654329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_35 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (41431747427443 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102191674863 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨35, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (41431747427443 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102191674863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_36 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82829454129339 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (275548420173 / 12500000000000 : ℝ))
      (E := (cell13104 ⟨36, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82829454129339 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (275548420173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_37 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82795437054279 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (220439134367 / 10000000000000 : ℝ))
      (E := (cell13104 ⟨37, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82795437054279 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (220439134367 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_38 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82761443599463 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204395355143 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨38, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82761443599463 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204395355143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_39 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (41363736867401 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (137774962217 / 6250000000000 : ℝ))
      (E := (cell13104 ⟨39, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (41363736867401 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (137774962217 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13105_20 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (8337695075587 / 10000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102105613823 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨20, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (8337695075587 / 10000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102105613823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_21 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (20835637885857 / 25000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204215226053 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨21, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (20835637885857 / 25000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204215226053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_22 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83308176454073 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (110210961431 / 5000000000000 : ℝ))
      (E := (cell13105 ⟨22, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83308176454073 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (110210961431 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_23 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41636912727579 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204223238659 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨23, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41636912727579 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204223238659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_24 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83239498514201 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (137764203703 / 6250000000000 : ℝ))
      (E := (cell13105 ⟨24, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83239498514201 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (137764203703 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_25 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83205195598887 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102115617399 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨25, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83205195598887 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102115617399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_26 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41585458338533 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (440847056953 / 20000000000000 : ℝ))
      (E := (cell13105 ⟨26, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41585458338533 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (440847056953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_27 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (16627332343351 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551059823659 / 25000000000000 : ℝ))
      (E := (cell13105 ⟨27, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (16627332343351 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551059823659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_28 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83102430686131 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204243324993 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨28, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83102430686131 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204243324993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_29 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (16613644710707 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204247319227 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨29, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (16613644710707 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204247319227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_30 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (83034040287469 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204251337507 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨30, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (83034040287469 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204251337507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_31 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (20749970214149 / 25000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204255322721 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨31, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (20749970214149 / 25000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204255322721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_32 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82965745229737 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551064833657 / 25000000000000 : ℝ))
      (E := (cell13105 ⟨32, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82965745229737 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551064833657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_33 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82931633375873 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102131687119 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨33, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82931633375873 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102131687119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_34 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41448772632071 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551066845921 / 25000000000000 : ℝ))
      (E := (cell13105 ⟨34, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41448772632071 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551066845921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_35 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41431740431919 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551067855531 / 25000000000000 : ℝ))
      (E := (cell13105 ⟨35, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41431740431919 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551067855531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_36 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (8282944014441 / 10000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2755344289 / 125000000000 : ℝ))
      (E := (cell13105 ⟨36, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (8282944014441 / 10000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2755344289 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_37 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (10349427884433 / 12500000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204279410951 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨37, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (10349427884433 / 12500000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204279410951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_38 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82761429626757 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (440856683987 / 20000000000000 : ℝ))
      (E := (cell13105 ⟨38, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82761429626757 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (440856683987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_39 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (413637298841 / 500000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (110214372891 / 5000000000000 : ℝ))
      (E := (cell13105 ⟨39, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (413637298841 / 500000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (110214372891 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13106_20 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83376936674567 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204099281763 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨20, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83376936674567 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204099281763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_21 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83342537468321 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (220410327687 / 10000000000000 : ℝ))
      (E := (cell13106 ⟨21, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83342537468321 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (220410327687 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_22 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83308162385157 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204107334547 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨22, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83308162385157 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204107334547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_23 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (20818452848107 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102055670701 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨23, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (20818452848107 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102055670701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_24 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83239484457651 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102057679427 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨24, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83239484457651 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102057679427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_25 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83205181548511 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102059665657 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨25, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83205181548511 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102059665657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_26 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83170902632861 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551030844559 / 25000000000000 : ℝ))
      (E := (cell13106 ⟨26, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83170902632861 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551030844559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_27 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41568323839357 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204127385109 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨27, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41568323839357 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204127385109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_28 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (332409666617 / 400000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102065706257 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨28, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (332409666617 / 400000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102065706257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_29 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (81121298367 / 97656250000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204135403843 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨29, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (81121298367 / 97656250000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204135403843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_30 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (83034026267891 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440827883853 / 20000000000000 : ℝ))
      (E := (cell13106 ⟨30, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (83034026267891 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440827883853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_31 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41499933421581 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440828680333 / 20000000000000 : ℝ))
      (E := (cell13106 ⟨31, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41499933421581 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440828680333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_32 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41482865611221 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440829493881 / 20000000000000 : ℝ))
      (E := (cell13106 ⟨32, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41482865611221 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440829493881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_33 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82931619374711 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204151447697 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨33, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82931619374711 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204151447697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_34 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82897531269109 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204155454469 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨34, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82897531269109 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204155454469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_35 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (5178966679683 / 6250000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204159490283 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨35, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (5178966679683 / 6250000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204159490283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_36 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41414713080809 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102081748389 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨36, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41414713080809 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102081748389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_37 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (16559081819757 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204167532709 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨37, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (16559081819757 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204167532709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_38 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41380707828093 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551042884807 / 25000000000000 : ℝ))
      (E := (cell13106 ⟨38, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41380707828093 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551042884807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_39 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (20681861450933 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204175515933 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨39, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (20681861450933 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204175515933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13107_20 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (16675384519083 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203987389943 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨20, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (16675384519083 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2203987389943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_21 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (20835630848841 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101995690887 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨21, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (20835630848841 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101995690887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_22 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (8330814831839 / 10000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101997718111 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨22, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (8330814831839 / 10000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1101997718111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_23 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (16654759466369 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440799887979 / 20000000000000 : ℝ))
      (E := (cell13107 ⟨23, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (16654759466369 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440799887979 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_24 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (5202466900203 / 6250000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (220400345421 / 10000000000000 : ℝ))
      (E := (cell13107 ⟨24, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (5202466900203 / 6250000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (220400345421 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_25 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (83205167500283 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204007482013 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨25, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (83205167500283 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204007482013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_26 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (83170888590801 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102005733729 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨26, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (83170888590801 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102005733729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_27 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41568316821409 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102007735667 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨27, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41568316821409 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102007735667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_28 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (81154690063 / 97656250000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204019495789 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨28, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (81154690063 / 97656250000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204019495789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_29 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (83068195504223 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102011742107 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨29, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (83068195504223 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102011742107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_30 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (16606802450091 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204027496777 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨30, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (16606802450091 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204027496777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_31 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (20749963207967 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102015767471 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨31, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (20749963207967 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102015767471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_32 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41482858608643 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204035541341 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨32, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41482858608643 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204035541341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_33 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (10366450671961 / 12500000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440807915107 / 20000000000000 : ℝ))
      (E := (cell13107 ⟨33, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (10366450671961 / 12500000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440807915107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_34 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82897517276213 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204043579659 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨34, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82897517276213 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204043579659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_35 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41431726444077 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (220404761287 / 10000000000000 : ℝ))
      (E := (cell13107 ⟨35, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41431726444077 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (220404761287 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_36 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41414706090481 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (275506452101 / 12500000000000 : ℝ))
      (E := (cell13107 ⟨36, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41414706090481 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (275506452101 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_37 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82795395124241 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204055650229 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨37, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82795395124241 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204055650229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_38 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82761401687749 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (551014913571 / 25000000000000 : ℝ))
      (E := (cell13107 ⟨38, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82761401687749 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (551014913571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_39 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41363715920699 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204063628569 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨39, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41363715920699 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204063628569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13108_20 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83376908518413 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101937746937 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨20, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83376908518413 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101937746937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_21 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83342509324557 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (220387954077 / 10000000000000 : ℝ))
      (E := (cell13108 ⟨21, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83342509324557 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (220387954077 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_22 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83308134253773 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (137742720853 / 6250000000000 : ℝ))
      (E := (cell13108 ⟨22, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83308134253773 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (137742720853 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_23 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83273783273411 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203887534139 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨23, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83273783273411 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203887534139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_24 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (5202466021937 / 6250000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203891545319 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨24, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (5202466021937 / 6250000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203891545319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_25 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83205153454201 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203895570033 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨25, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83205153454201 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203895570033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_26 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83170874550887 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203899610893 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨26, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83170874550887 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203899610893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_27 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (83136619609067 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (440780722359 / 20000000000000 : ℝ))
      (E := (cell13108 ⟨27, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (83136619609067 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (440780722359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_28 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (41551194298459 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550976908331 / 25000000000000 : ℝ))
      (E := (cell13108 ⟨28, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (41551194298459 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550976908331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_29 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (41534090741391 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550977904717 / 25000000000000 : ℝ))
      (E := (cell13108 ⟨29, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (41534090741391 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550977904717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_30 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (2075849955879 / 2500000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203915628599 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨30, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (2075849955879 / 2500000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203915628599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_31 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (16599967764543 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203919663977 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨31, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (16599967764543 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203919663977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_32 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (8296570321427 / 10000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (440784733527 / 20000000000000 : ℝ))
      (E := (cell13108 ⟨32, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (8296570321427 / 10000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (440784733527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_33 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (20732897844701 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101963849567 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨33, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (20732897844701 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1101963849567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_34 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (16579500657091 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203931700611 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨34, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (16579500657091 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203931700611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_35 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (41431719451759 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203935731219 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨35, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (41431719451759 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203935731219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_36 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (41414699101221 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203939732601 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨36, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (41414699101221 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203939732601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_37 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (10349422643979 / 12500000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203943763513 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨37, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (10349422643979 / 12500000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203943763513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_38 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (82761387721447 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (137746735319 / 6250000000000 : ℝ))
      (E := (cell13108 ⟨38, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (82761387721447 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (137746735319 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_39 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (20681854470299 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275493974467 / 12500000000000 : ℝ))
      (E := (cell13108 ⟨39, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (20681854470299 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275493974467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13109_20 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83376894443563 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220376365187 / 10000000000000 : ℝ))
      (E := (cell13109 ⟨20, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83376894443563 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220376365187 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_21 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (833424952559 / 1000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550941923879 / 25000000000000 : ℝ))
      (E := (cell13109 ⟨21, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (833424952559 / 1000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550941923879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_22 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83308120191303 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220377168519 / 10000000000000 : ℝ))
      (E := (cell13109 ⟨22, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83308120191303 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220377168519 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_23 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (666190153737 / 800000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101887841261 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨23, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (666190153737 / 800000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101887841261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_24 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83239442300883 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203779749003 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨24, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83239442300883 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203779749003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_25 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (10400642426283 / 12500000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203783712241 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨25, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (10400642426283 / 12500000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203783712241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_26 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83170860513117 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203787750083 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨26, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83170860513117 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203787750083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_27 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83136605577459 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203791748013 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨27, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83136605577459 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203791748013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_28 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (83102374571467 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (275474470827 / 12500000000000 : ℝ))
      (E := (cell13109 ⟨28, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (83102374571467 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (275474470827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_29 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41534083731741 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203799807809 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨29, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41534083731741 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203799807809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_30 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41516992111003 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203803814731 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨30, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41516992111003 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203803814731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_31 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82999824815703 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220380778877 / 10000000000000 : ℝ))
      (E := (cell13109 ⟨31, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82999824815703 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220380778877 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_32 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82965689213393 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203811848287 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨32, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82965689213393 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203811848287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_33 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41465788692029 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101907909247 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨33, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41465788692029 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101907909247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_34 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (16579497859367 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (17217342781 / 781250000000 : ℝ))
      (E := (cell13109 ⟨34, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (16579497859367 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (17217342781 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_35 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41431712460509 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220382384533 / 10000000000000 : ℝ))
      (E := (cell13109 ⟨35, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41431712460509 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220382384533 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_36 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41414692113029 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203827902849 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨36, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41414692113029 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203827902849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_37 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41397683590779 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203831872561 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨37, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41397683590779 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203831872561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_38 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41380686878639 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203835930429 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨38, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41380686878639 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203835930429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_39 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82727403923127 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550959989667 / 25000000000000 : ℝ))
      (E := (cell13109 ⟨39, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82727403923127 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550959989667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13110_20 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41688440185431 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (440730372787 / 20000000000000 : ℝ))
      (E := (cell13110 ⟨20, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41688440185431 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (440730372787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_21 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83342481189391 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101827923007 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨21, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83342481189391 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101827923007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_22 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41654053065491 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (68864371589 / 3125000000000 : ℝ))
      (E := (cell13110 ⟨22, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41654053065491 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (68864371589 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_23 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41636877581493 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203663885047 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨23, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41636877581493 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203663885047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_24 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83239428252921 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203667890029 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨24, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83239428252921 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203667890029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_25 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83205125368473 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101835954319 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨25, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83205125368473 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101835954319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_26 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (20792711619373 / 25000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (440735188697 / 20000000000000 : ℝ))
      (E := (cell13110 ⟨26, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (20792711619373 / 25000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (440735188697 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_27 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41568295773997 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203679938469 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨27, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41568295773997 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203679938469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_28 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41551180274079 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (220368395417 / 10000000000000 : ℝ))
      (E := (cell13110 ⟨28, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41551180274079 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (220368395417 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_29 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83068153446323 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203687933981 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨29, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83068153446323 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203687933981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_30 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (83033970210993 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101845998311 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨30, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (83033970210993 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101845998311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_31 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82999810810829 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (22036959679 / 1000000000000 : ℝ))
      (E := (cell13110 ⟨31, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82999810810829 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (22036959679 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_32 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (16593135042931 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (22037000247 / 1000000000000 : ℝ))
      (E := (cell13110 ⟨32, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (16593135042931 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (22037000247 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_33 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82931563391449 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203703992239 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨33, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82931563391449 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203703992239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_34 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82897475310351 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203708047089 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨34, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82897475310351 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203708047089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_35 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41431705470327 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101856006937 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨35, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41431705470327 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101856006937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_36 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (2588417820369 / 3125000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203716068863 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨36, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (2588417820369 / 3125000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203716068863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_37 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41397676606709 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (440744018961 / 20000000000000 : ℝ))
      (E := (cell13110 ⟨37, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41397676606709 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (440744018961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_38 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41380679897621 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (3443318893 / 156250000000 : ℝ))
      (E := (cell13110 ⟨38, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41380679897621 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (3443318893 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_39 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82727389967191 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101864058683 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨39, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82727389967191 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101864058683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13111_20 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (8337686630031 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101770006717 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨20, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (8337686630031 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101770006717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_21 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (83342467125031 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440708810121 / 20000000000000 : ℝ))
      (E := (cell13111 ⟨21, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (83342467125031 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440708810121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_22 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (10413511509101 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (275443504237 / 12500000000000 : ℝ))
      (E := (cell13111 ⟨22, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (10413511509101 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (275443504237 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_23 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (83273741110993 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101776041663 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨23, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (83273741110993 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101776041663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_24 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (83239414207103 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101778042611 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨24, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (83239414207103 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101778042611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_25 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41602555664413 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203560100791 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨25, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41602555664413 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203560100791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_26 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (8317083244401 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101782066323 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨26, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (8317083244401 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101782066323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_27 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (2598018047521 / 3125000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203568124683 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨27, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (2598018047521 / 3125000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203568124683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_28 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (83102346526991 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203572137483 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨28, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (83102346526991 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203572137483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_29 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (16613627886261 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203576172969 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨29, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (16613627886261 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203576172969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_30 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (83033956202119 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101790087137 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨30, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (83033956202119 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101790087137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_31 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (16599959361619 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440716840273 / 20000000000000 : ℝ))
      (E := (cell13111 ⟨31, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (16599959361619 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440716840273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_32 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41482830609027 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203588196877 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨32, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41482830609027 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203588196877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_33 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41465774700489 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203592220367 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨33, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41465774700489 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203592220367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_34 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (82897461326003 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101798106987 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨34, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (82897461326003 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101798106987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_35 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (10357924620303 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550900059213 / 25000000000000 : ℝ))
      (E := (cell13111 ⟨35, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (10357924620303 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550900059213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_36 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (20707339069923 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101802115321 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨36, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (20707339069923 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101802115321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_37 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (82795339247411 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203608254101 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨37, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (82795339247411 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203608254101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_38 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41380672917669 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101806153559 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨38, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41380672917669 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101806153559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_39 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (16545475202677 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101808135917 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨39, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (16545475202677 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101808135917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13112_20 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83376852231907 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550857054251 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨20, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83376852231907 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550857054251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_21 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83342453062819 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203432250949 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨21, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83342453062819 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203432250949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_22 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41654039008391 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101718144713 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨22, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41654039008391 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101718144713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_23 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41636863530573 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203440277361 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨23, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41636863530573 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203440277361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_24 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83239400163431 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550861069043 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨24, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83239400163431 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550861069043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_25 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83205097291323 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101724144351 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨25, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83205097291323 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101724144351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_26 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (649772018849 / 781250000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550863079391 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨26, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (649772018849 / 781250000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550863079391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_27 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (83136563495493 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101728153327 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨27, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (83136563495493 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101728153327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_28 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (16620466501593 / 20000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203460375061 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨28, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (16620466501593 / 20000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203460375061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_29 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (20767031354607 / 25000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203464349189 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨29, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (20767031354607 / 25000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203464349189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_30 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41516971097693 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101734173843 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨30, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41516971097693 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101734173843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_31 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82999782807499 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101736186009 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨31, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82999782807499 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101736186009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_32 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (10370705902949 / 12500000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203476423413 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨32, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (10370705902949 / 12500000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203476423413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_33 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82931535412643 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (110174022213 / 5000000000000 : ℝ))
      (E := (cell13112 ⟨33, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82931535412643 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (110174022213 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_34 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82897447343791 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203484435269 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨34, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82897447343791 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203484435269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_35 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (8286338298633 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550872113899 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨35, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (8286338298633 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550872113899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_36 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (8282934230971 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203492446881 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨36, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (8282934230971 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203492446881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_37 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (5174707830221 / 6250000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203496467881 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨37, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (5174707830221 / 6250000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203496467881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_38 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41380665938783 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550875129621 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨38, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41380665938783 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550875129621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_39 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82727362061711 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101752240417 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨39, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82727362061711 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101752240417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13113_20 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (83376838165653 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440663294929 / 20000000000000 : ℝ))
      (E := (cell13113 ⟨20, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (83376838165653 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440663294929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_21 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (16668487800551 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203320505389 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨21, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (16668487800551 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203320505389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_22 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (83308063962901 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203324482349 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨22, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (83308063962901 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203324482349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_23 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (16654742602689 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (110166426277 / 5000000000000 : ℝ))
      (E := (cell13113 ⟨23, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (16654742602689 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (110166426277 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_24 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (5202461632619 / 6250000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203332521289 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨24, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (5202461632619 / 6250000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203332521289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_25 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (20801270813991 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440667306161 / 20000000000000 : ℝ))
      (E := (cell13113 ⟨25, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (20801270813991 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440667306161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_26 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (20792701095869 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203340556699 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨26, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (20792701095869 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203340556699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_27 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (16627309894491 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550836135717 / 25000000000000 : ℝ))
      (E := (cell13113 ⟨27, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (16627309894491 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550836135717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_28 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (2077557962277 / 2500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (5508371521 / 250000000000 : ℝ))
      (E := (cell13113 ⟨28, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (2077557962277 / 2500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (5508371521 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_29 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (83068111407691 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101676289849 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨29, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (83068111407691 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101676289849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_30 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (83033928190791 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101678316983 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨30, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (83033928190791 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101678316983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_31 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41499884404521 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (137710037313 / 6250000000000 : ℝ))
      (E := (cell13113 ⟨31, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41499884404521 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (137710037313 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_32 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41482816615633 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440672929143 / 20000000000000 : ℝ))
      (E := (cell13113 ⟨32, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41482816615633 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440672929143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_33 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (20732880356611 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203368663919 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨33, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (20732880356611 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203368663919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_34 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41448716681857 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203372652331 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨34, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41448716681857 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203372652331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_35 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (8286336901237 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101688335053 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨35, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (8286336901237 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101688335053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_36 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41414664170931 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203380717579 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨36, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41414664170931 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203380717579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_37 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (16559062264359 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (137711546009 / 6250000000000 : ℝ))
      (E := (cell13113 ⟨37, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (16559062264359 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (137711546009 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_38 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41380658960963 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (110169436281 / 5000000000000 : ℝ))
      (E := (cell13113 ⟨38, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41380658960963 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (110169436281 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_39 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (10340918514021 / 12500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440678548873 / 20000000000000 : ℝ))
      (E := (cell13113 ⟨39, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (10340918514021 / 12500000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440678548873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13114_20 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83376824101547 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203204728041 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨20, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83376824101547 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203204728041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_21 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83342424944837 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101604377793 / 50000000000000 : ℝ))
      (E := (cell13114 ⟨21, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83342424944837 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101604377793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_22 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83308049911167 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (137700795587 / 6250000000000 : ℝ))
      (E := (cell13114 ⟨22, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83308049911167 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (137700795587 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_23 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83273698967889 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550804192369 / 25000000000000 : ℝ))
      (E := (cell13114 ⟨23, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83273698967889 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550804192369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_24 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83239372082521 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440644152433 / 20000000000000 : ℝ))
      (E := (cell13114 ⟨24, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83239372082521 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440644152433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_25 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83205069222749 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203224768667 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨25, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83205069222749 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203224768667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_26 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83170790356423 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440645758319 / 20000000000000 : ℝ))
      (E := (cell13114 ⟨26, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83170790356423 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440645758319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_27 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83136535451559 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (88129313333 / 4000000000000 : ℝ))
      (E := (cell13114 ⟨27, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83136535451559 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (88129313333 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_28 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (16620460895267 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203236837501 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨28, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (16620460895267 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203236837501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_29 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (83068097399093 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203240864499 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨29, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (83068097399093 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203240864499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_30 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (41516957094167 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101622428729 / 50000000000000 : ℝ))
      (E := (cell13114 ⟨30, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (41516957094167 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101622428729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_31 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (41499877406361 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (110162443817 / 5000000000000 : ℝ))
      (E := (cell13114 ⟨31, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (41499877406361 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (110162443817 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_32 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82965619241077 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203252863783 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨32, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82965619241077 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203252863783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_33 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (41465753721191 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203256879343 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨33, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (41465753721191 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203256879343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_34 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (20724354846443 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440652184761 / 20000000000000 : ℝ))
      (E := (cell13114 ⟨34, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (20724354846443 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440652184761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_35 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (2589479845017 / 3125000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101632469527 / 50000000000000 : ℝ))
      (E := (cell13114 ⟨35, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (2589479845017 / 3125000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101632469527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_36 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82829314376147 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203268925353 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨36, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82829314376147 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203268925353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_37 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (16559059472437 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203272941461 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨37, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (16559059472437 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203272941461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_38 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82761303968417 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440655397453 / 20000000000000 : ℝ))
      (E := (cell13114 ⟨38, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82761303968417 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (440655397453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_39 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (41363667082377 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220328100367 / 10000000000000 : ℝ))
      (E := (cell13114 ⟨39, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (41363667082377 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220328100367 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13115_20 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (20844202509897 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (220309303551 / 10000000000000 : ℝ))
      (E := (cell13115 ⟨20, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (20844202509897 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (220309303551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_21 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41671205444533 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101548500769 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨21, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41671205444533 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101548500769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_22 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83308035861579 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440620206111 / 20000000000000 : ℝ))
      (E := (cell13115 ⟨22, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83308035861579 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440620206111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_23 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83273684924477 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203105067559 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨23, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83273684924477 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203105067559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_24 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83239358045281 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550777264303 / 25000000000000 : ℝ))
      (E := (cell13115 ⟨24, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83239358045281 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550777264303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_25 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (20801263797919 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550778265181 / 25000000000000 : ℝ))
      (E := (cell13115 ⟨25, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (20801263797919 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550778265181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_26 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83170776331511 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203117080709 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨26, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83170776331511 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203117080709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_27 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83136521432803 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203121119543 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨27, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83136521432803 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203121119543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_28 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (83102290463731 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550781280217 / 25000000000000 : ℝ))
      (E := (cell13115 ⟨28, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (83102290463731 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550781280217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_29 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41534041696317 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203129145063 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨29, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41534041696317 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203129145063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_30 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (5189618761751 / 6250000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (68847910477 / 3125000000000 : ℝ))
      (E := (cell13115 ⟨30, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (5189618761751 / 6250000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (68847910477 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_31 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82999740818539 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550784287859 / 25000000000000 : ℝ))
      (E := (cell13115 ⟨31, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82999740818539 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550784287859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_32 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (3318624210121 / 4000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550785298703 / 25000000000000 : ℝ))
      (E := (cell13115 ⟨32, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (3318624210121 / 4000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550785298703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_33 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41465746730227 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203145207779 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨33, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41465746730227 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203145207779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_34 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (16579481081993 / 20000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440629838209 / 20000000000000 : ℝ))
      (E := (cell13115 ⟨34, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (16579481081993 / 20000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440629838209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_35 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82863341070851 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203153203769 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨35, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82863341070851 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203153203769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_36 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (20707325103141 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101578623141 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨36, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (20707325103141 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101578623141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_37 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82795283404707 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (110158062999 / 5000000000000 : ℝ))
      (E := (cell13115 ⟨37, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82795283404707 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (110158062999 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_38 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82761290017039 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (55079131117 / 2500000000000 : ℝ))
      (E := (cell13115 ⟨38, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82761290017039 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (55079131117 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_39 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (8272732021947 / 10000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440633851749 / 20000000000000 : ℝ))
      (E := (cell13115 ⟨39, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (8272732021947 / 10000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440633851749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13116_20 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20355663081 / 24414062500 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101490640209 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨20, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20355663081 / 24414062500 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101490640209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_21 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (83342396835441 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202985301589 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨21, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (83342396835441 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202985301589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_22 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (16661604362827 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202989327479 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨22, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (16661604362827 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2202989327479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_23 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (8327367088321 / 10000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (11014966807 / 500000000000 : ℝ))
      (E := (cell13116 ⟨23, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (8327367088321 / 10000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (11014966807 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_24 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (16647868802037 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101498674009 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨24, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (16647868802037 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101498674009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_25 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (16641008232549 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203001348543 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨25, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (16641008232549 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203001348543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_26 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (83170762308741 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440601073117 / 20000000000000 : ℝ))
      (E := (cell13116 ⟨26, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (83170762308741 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440601073117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_27 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20784126854047 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203009401523 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨27, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20784126854047 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203009401523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_28 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (41551138226633 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (11015067 / 500000000 : ℝ))
      (E := (cell13116 ⟨28, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (41551138226633 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (11015067 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_29 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (41534034694157 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (137688588837 / 6250000000000 : ℝ))
      (E := (cell13116 ⟨29, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (41534034694157 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (137688588837 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_30 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (16606777237967 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203021408837 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨30, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (16606777237967 / 20000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203021408837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_31 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20749931706623 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203025422299 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨31, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20749931706623 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203025422299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_32 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20741397816777 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203029463011 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨32, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20741397816777 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203029463011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_33 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82931479480661 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (27537918417 / 1250000000000 : ℝ))
      (E := (cell13116 ⟨33, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82931479480661 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (27537918417 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_34 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82897391436291 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101518756351 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨34, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82897391436291 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101518756351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_35 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82863327103291 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550760380731 / 25000000000000 : ℝ))
      (E := (cell13116 ⟨35, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82863327103291 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550760380731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_36 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82829286451113 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203045504289 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨36, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82829286451113 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203045504289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_37 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (1034940868117 / 1250000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440609903111 / 20000000000000 : ℝ))
      (E := (cell13116 ⟨37, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (1034940868117 / 1250000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440609903111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_38 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (8276127606779 / 10000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203053556609 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨38, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (8276127606779 / 10000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203053556609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_39 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20681826569079 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550764392089 / 25000000000000 : ℝ))
      (E := (cell13116 ⟨39, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20681826569079 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550764392089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13117_20 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (8337678192211 / 10000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (55071740943 / 2500000000000 : ℝ))
      (E := (cell13117 ⟨20, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (8337678192211 / 10000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (55071740943 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_21 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83342382783961 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202873655741 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨21, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83342382783961 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202873655741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_22 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (20827001942209 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101438810081 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨22, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (20827001942209 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101438810081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_23 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41636828422043 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202881651003 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨23, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41636828422043 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202881651003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_24 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83239329977231 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202885692999 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨24, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83239329977231 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202885692999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_25 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (20801256783989 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202889690559 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨25, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (20801256783989 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202889690559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_26 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83170748288111 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202893704683 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨26, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83170748288111 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202893704683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_27 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83136493401713 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (8811590951 / 400000000000 : ℝ))
      (E := (cell13117 ⟨27, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83136493401713 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (8811590951 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_28 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83102262444939 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101450866701 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨28, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83102262444939 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101450866701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_29 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (83068055386131 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (137681609501 / 6250000000000 : ℝ))
      (E := (cell13117 ⟨29, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (83068055386131 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (137681609501 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_30 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (324351063257 / 390625000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202909736727 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨30, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (324351063257 / 390625000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202909736727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_31 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41499856418291 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (137682109219 / 6250000000000 : ℝ))
      (E := (cell13117 ⟨31, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41499856418291 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (137682109219 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_32 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41482788641663 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202917785577 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨32, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41482788641663 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202917785577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_33 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41465732751501 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101460896667 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨33, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41465732751501 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101460896667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_34 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (331589509859 / 400000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202925830129 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨34, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (331589509859 / 400000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202925830129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_35 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (10357914142233 / 12500000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (44058596757 / 2000000000000 : ℝ))
      (E := (cell13117 ⟨35, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (10357914142233 / 12500000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (44058596757 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_36 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (82829272491793 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202933816761 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨36, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (82829272491793 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202933816761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_37 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (82795255496143 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (440587576867 / 20000000000000 : ℝ))
      (E := (cell13117 ⟨37, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (82795255496143 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (440587576867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_38 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (82761262120671 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202941864311 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨38, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (82761262120671 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202941864311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_39 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (82727292335289 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (137684117109 / 6250000000000 : ℝ))
      (E := (cell13117 ⟨39, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (82727292335289 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (137684117109 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13118_20 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83376767866591 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202757932463 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨20, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83376767866591 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202757932463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_21 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83342368734627 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202761947311 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨21, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83342368734627 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202761947311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_22 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83307993725681 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202765966971 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨22, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83307993725681 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202765966971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_23 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41636821403553 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440553998951 / 20000000000000 : ℝ))
      (E := (cell13118 ⟨23, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41636821403553 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440553998951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_24 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83239315946419 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101387016871 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨24, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83239315946419 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101387016871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_25 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (20801253277827 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202778028339 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨25, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (20801253277827 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202778028339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_26 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41585367134811 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101391019773 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨26, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41585367134811 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101391019773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_27 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83136479389377 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101393034871 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨27, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83136479389377 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101393034871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_28 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (2596945263711 / 3125000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (220279006257 / 10000000000000 : ℝ))
      (E := (cell13118 ⟨28, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (2596945263711 / 3125000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (220279006257 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_29 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (83068041386087 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101397039203 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨29, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (83068041386087 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101397039203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_30 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (20758464549971 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (110139905947 / 5000000000000 : ℝ))
      (E := (cell13118 ⟨30, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (20758464549971 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (110139905947 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_31 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (10374962356101 / 12500000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101401063527 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨31, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (10374962356101 / 12500000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101401063527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_32 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41482781650839 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101403051957 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨32, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41482781650839 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101403051957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_33 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82931451527477 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101405054539 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨33, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82931451527477 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101405054539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_34 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82897363495343 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101407071663 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨34, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82897363495343 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101407071663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_35 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (10357912396821 / 12500000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (550704537137 / 25000000000000 : ℝ))
      (E := (cell13118 ⟨35, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (10357912396821 / 12500000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (550704537137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_36 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (16565851706921 / 20000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202822183699 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨36, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (16565851706921 / 20000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202822183699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_37 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (2587351298283 / 3125000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202826190173 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨37, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (2587351298283 / 3125000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202826190173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_38 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82761248175681 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202830226529 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨38, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82761248175681 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202830226529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_39 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82727278396391 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202834233669 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨39, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82727278396391 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202834233669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13119_20 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83376753813217 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101323169801 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨20, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83376753813217 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101323169801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_21 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (20835588671859 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101325175663 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨21, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (20835588671859 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101325175663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_22 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (8330797968467 / 10000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101327183953 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨22, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (8330797968467 / 10000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101327183953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_23 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (20818407193067 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220265833427 / 10000000000000 : ℝ))
      (E := (cell13119 ⟨23, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (20818407193067 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220265833427 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_24 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83239301917749 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (275332796281 / 12500000000000 : ℝ))
      (E := (cell13119 ⟨24, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83239301917749 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (275332796281 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_25 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83204999088801 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101333180941 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨25, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83204999088801 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101333180941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_26 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83170720253273 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202670370173 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨26, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83170720253273 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202670370173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_27 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (4156823268959 / 5000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (881069759 / 40000000000 : ℝ))
      (E := (cell13119 ⟨27, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (4156823268959 / 5000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (881069759 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_28 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41551117217351 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220267844601 / 10000000000000 : ℝ))
      (E := (cell13119 ⟨28, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41551117217351 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220267844601 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_29 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83068027388179 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202682459093 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨29, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83068027388179 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202682459093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_30 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (83033844208113 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202686438367 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨30, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (83033844208113 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202686438367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_31 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (1296870075987 / 1562500000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101345221899 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨31, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (1296870075987 / 1562500000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101345221899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_32 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (16593109864433 / 20000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202694476619 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨32, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (16593109864433 / 20000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202694476619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_33 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41465718777043 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101349239607 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨33, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41465718777043 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101349239607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_34 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (82897349528067 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101351255471 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨34, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (82897349528067 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101351255471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_35 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (20715821303351 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (275338314211 / 12500000000000 : ℝ))
      (E := (cell13119 ⟨35, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (20715821303351 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (275338314211 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_36 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41414622289773 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220271054641 / 10000000000000 : ℝ))
      (E := (cell13119 ⟨36, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41414622289773 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220271054641 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_37 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (82795227596099 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202714550501 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨37, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (82795227596099 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202714550501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_38 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (4138061711641 / 5000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (55067964613 / 2500000000000 : ℝ))
      (E := (cell13119 ⟨38, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (4138061711641 / 5000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (55067964613 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_39 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (82727264459621 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220272258937 / 10000000000000 : ℝ))
      (E := (cell13119 ⟨39, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (82727264459621 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220272258937 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13120_20 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (20844184940497 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202534684183 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨20, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (20844184940497 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202534684183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_21 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (8334234064239 / 10000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202538692759 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨21, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (8334234064239 / 10000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202538692759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_22 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83307965645801 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202542706239 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨22, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83307965645801 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202542706239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_23 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (20818403684893 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2150924539 / 97656250000 : ℝ))
      (E := (cell13120 ⟨23, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (20818403684893 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2150924539 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_24 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83239287891221 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202550760929 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨24, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83239287891221 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202550760929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_25 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41602492534217 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (17620437997 / 800000000000 : ℝ))
      (E := (cell13120 ⟨25, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41602492534217 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (17620437997 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_26 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83170706239063 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (137659922189 / 6250000000000 : ℝ))
      (E := (cell13120 ⟨26, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83170706239063 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (137659922189 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_27 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83136451371121 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202562779507 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨27, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83136451371121 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202562779507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_28 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83102220432789 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101283412609 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨28, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83102220432789 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101283412609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_29 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (83068013392407 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (550642708887 / 25000000000000 : ℝ))
      (E := (cell13120 ⟨29, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (83068013392407 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (550642708887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_30 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41516915109239 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (440514962423 / 20000000000000 : ℝ))
      (E := (cell13120 ⟨30, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41516915109239 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (440514962423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_31 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82999670879663 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202578873463 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨31, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82999670879663 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202578873463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_32 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41482767672393 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (440516569019 / 20000000000000 : ℝ))
      (E := (cell13120 ⟨32, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41482767672393 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (440516569019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_33 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82931423582827 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101293451873 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨33, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82931423582827 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101293451873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_34 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82897335562923 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220259087433 / 10000000000000 : ℝ))
      (E := (cell13120 ⟨34, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82897335562923 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220259087433 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_35 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82863271254371 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202594933271 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨35, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82863271254371 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202594933271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_36 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41414615313309 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (34415607889 / 1562500000000 : ℝ))
      (E := (cell13120 ⟨36, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41414615313309 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (34415607889 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_37 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82795213649271 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (550650726651 / 25000000000000 : ℝ))
      (E := (cell13120 ⟨37, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82795213649271 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (550650726651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_38 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82761220292087 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (137662933643 / 6250000000000 : ℝ))
      (E := (cell13120 ⟨38, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82761220292087 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (137662933643 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_39 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41363625262489 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (137663183803 / 6250000000000 : ℝ))
      (E := (cell13120 ⟨39, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41363625262489 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (137663183803 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13121_20 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83376725712903 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101211541423 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨20, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83376725712903 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101211541423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_21 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (1302223853117 / 1562500000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101213544149 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨21, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (1302223853117 / 1562500000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101213544149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_22 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (20826987902269 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202431098701 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨22, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (20826987902269 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202431098701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_23 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83273600709017 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202435117369 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨23, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83273600709017 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202435117369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_24 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83239273866833 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202439147377 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨24, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83239273866833 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202439147377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_25 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83204971050207 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550610797893 / 25000000000000 : ℝ))
      (E := (cell13121 ⟨25, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83204971050207 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550610797893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_26 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83170692226991 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (275305899263 / 12500000000000 : ℝ))
      (E := (cell13121 ⟨26, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83170692226991 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (275305899263 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_27 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83136437365201 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550612803941 / 25000000000000 : ℝ))
      (E := (cell13121 ⟨27, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83136437365201 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550612803941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_28 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41551103216507 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (440491040039 / 20000000000000 : ℝ))
      (E := (cell13121 ⟨28, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41551103216507 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (440491040039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_29 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (20766999849693 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101229603887 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨29, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (20766999849693 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101229603887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_30 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (83033816230977 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202463240189 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨30, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (83033816230977 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202463240189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_31 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (20749914224573 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (88098689613 / 4000000000000 : ℝ))
      (E := (cell13121 ⟨31, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (20749914224573 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (88098689613 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_32 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (4148276068477 / 5000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (275308908493 / 12500000000000 : ℝ))
      (E := (cell13121 ⟨32, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (4148276068477 / 5000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (275308908493 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_33 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (829314096137 / 1000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (220247526543 / 10000000000000 : ℝ))
      (E := (cell13121 ⟨33, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (829314096137 / 1000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (220247526543 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_34 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82897321599911 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (110123964607 / 5000000000000 : ℝ))
      (E := (cell13121 ⟨34, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82897321599911 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (110123964607 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_35 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (20715814324367 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202483289961 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨35, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (20715814324367 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202483289961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_36 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82829216675819 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550621829463 / 25000000000000 : ℝ))
      (E := (cell13121 ⟨36, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82829216675819 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550621829463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_37 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82795199704571 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202491317203 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨37, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82795199704571 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202491317203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_38 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41380603176741 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101247673287 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨38, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41380603176741 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101247673287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_39 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41363618296231 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202499346869 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨39, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41363618296231 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202499346869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13122_20 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41688355832981 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202311535589 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨20, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41688355832981 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202311535589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_21 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (10417789069841 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101157768971 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨21, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (10417789069841 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101157768971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_22 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (20826984393623 / 25000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550579886323 / 25000000000000 : ℝ))
      (E := (cell13122 ⟨22, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (20826984393623 / 25000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550579886323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_23 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (20818396670151 / 25000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101161780477 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨23, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (20818396670151 / 25000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101161780477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_24 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (16647851968917 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202327588003 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨24, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (16647851968917 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202327588003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_25 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83204957034119 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202331570849 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨25, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83204957034119 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202331570849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_26 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41585339108529 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202335570491 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨26, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41585339108529 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202335570491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_27 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83136423361417 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550584897327 / 25000000000000 : ℝ))
      (E := (cell13122 ⟨27, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83136423361417 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550584897327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_28 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (664817539483 / 800000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202343629447 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨28, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (664817539483 / 800000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202343629447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_29 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (10383498175909 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202347634299 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨29, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (10383498175909 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202347634299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_30 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (83033802245611 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101175832017 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨30, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (83033802245611 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101175832017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_31 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (16599928583811 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440471132307 / 20000000000000 : ℝ))
      (E := (cell13122 ⟨31, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (16599928583811 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440471132307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_32 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41482753698213 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440471937313 / 20000000000000 : ℝ))
      (E := (cell13122 ⟨32, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41482753698213 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440471937313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_33 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (16586279129341 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202363681509 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨33, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (16586279129341 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202363681509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_34 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (8289730763903 / 10000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202367705723 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨34, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (8289730763903 / 10000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202367705723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_35 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41431621671347 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (275296462637 / 12500000000000 : ℝ))
      (E := (cell13122 ⟨35, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41431621671347 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (275296462637 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_36 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82829202727149 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202375726583 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨36, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82829202727149 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202375726583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_37 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41397592881 / 50000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101189891147 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨37, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41397592881 / 50000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101189891147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_38 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82761192417003 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101191875319 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨38, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82761192417003 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101191875319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_39 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82727222662071 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202387807433 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨39, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82727222662071 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202387807433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13123_20 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (16675339524233 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (68818749503 / 3125000000000 : ℝ))
      (E := (cell13123 ⟨20, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (16675339524233 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (68818749503 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_21 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (5208893657507 / 6250000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (44044079667 / 2000000000000 : ℝ))
      (E := (cell13123 ⟨21, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (5208893657507 / 6250000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (44044079667 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_22 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (1666158470841 / 2000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (44044159753 / 2000000000000 : ℝ))
      (E := (cell13123 ⟨22, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (1666158470841 / 2000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (44044159753 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_23 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (20818393163583 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101106000153 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨23, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (20818393163583 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101106000153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_24 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83239245824477 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202216024397 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨24, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83239245824477 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202216024397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_25 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (8320494302017 / 10000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220222000433 / 10000000000000 : ℝ))
      (E := (cell13123 ⟨25, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (8320494302017 / 10000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220222000433 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_26 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83170664209263 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101112029783 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨26, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83170664209263 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101112029783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_27 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83136409359771 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101114037793 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨27, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83136409359771 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101114037793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_28 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (1298471538123 / 1562500000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202232054471 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨28, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (1298471538123 / 1562500000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202232054471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_29 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83067971417907 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550559014149 / 25000000000000 : ℝ))
      (E := (cell13123 ⟨29, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83067971417907 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550559014149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_30 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (83033788262379 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202240083651 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨30, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (83033788262379 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202240083651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_31 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82999628941951 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101122068547 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨31, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82999628941951 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101122068547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_32 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (16593098685089 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202248100961 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨32, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (16593098685089 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202248100961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_33 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (41465690840921 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202252151987 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨33, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (41465690840921 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202252151987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_34 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82897293680279 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220225617373 / 10000000000000 : ℝ))
      (E := (cell13123 ⟨34, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82897293680279 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220225617373 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_35 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82863229390051 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101130083339 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨35, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82863229390051 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101130083339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_36 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (1294206074697 / 1562500000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101132094893 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨36, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (1294206074697 / 1562500000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101132094893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_37 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (20698792955389 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202268184447 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨37, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (20698792955389 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202268184447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_38 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82761178482651 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202272209223 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨38, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82761178482651 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202272209223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_39 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82727208733807 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202276205013 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨39, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82727208733807 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202276205013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13124_20 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83376683578511 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (137630526773 / 6250000000000 : ℝ))
      (E := (cell13124 ⟨20, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83376683578511 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (137630526773 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_21 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83342284483637 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (88083696981 / 4000000000000 : ℝ))
      (E := (cell13124 ⟨21, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83342284483637 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (88083696981 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_22 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83307909511749 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101048212887 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨22, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83307909511749 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101048212887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_23 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (416367793151 / 500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (88084017417 / 4000000000000 : ℝ))
      (E := (cell13124 ⟨23, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (416367793151 / 500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (88084017417 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_24 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (20809807951627 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202104456559 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨24, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (20809807951627 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202104456559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_25 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (2080123225209 / 2500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (137631780751 / 6250000000000 : ℝ))
      (E := (cell13124 ⟨25, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (2080123225209 / 2500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (137631780751 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_26 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (16634130040721 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (34408007593 / 1562500000000 : ℝ))
      (E := (cell13124 ⟨26, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (16634130040721 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (34408007593 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_27 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83136395360261 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101058249577 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨27, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83136395360261 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101058249577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_28 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (10387770555813 / 12500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202120533773 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨28, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (10387770555813 / 12500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202120533773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_29 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83067957430677 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (440424906639 / 20000000000000 : ℝ))
      (E := (cell13124 ⟨29, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83067957430677 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (440424906639 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_30 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (83033774281281 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101064278797 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨30, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (83033774281281 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101064278797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_31 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (4149980748349 / 5000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (550533137463 / 25000000000000 : ℝ))
      (E := (cell13124 ⟨31, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (4149980748349 / 5000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (550533137463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_32 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (20741369864149 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (550534142433 / 25000000000000 : ℝ))
      (E := (cell13124 ⟨32, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (20741369864149 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (550534142433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_33 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82931367719109 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202140618241 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨33, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82931367719109 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202140618241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_34 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82897279723657 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (440428927503 / 20000000000000 : ℝ))
      (E := (cell13124 ⟨34, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82897279723657 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (440428927503 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_35 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (5178950964971 / 6250000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202148628037 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨35, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (5178950964971 / 6250000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202148628037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_36 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (16565834967239 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202152648767 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨36, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (16565834967239 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202152648767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_37 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82795157883239 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202156641097 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨37, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82795157883239 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202156641097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_38 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (41380582275213 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202160663587 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨38, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (41380582275213 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202160663587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_39 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (20681798701917 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101082357951 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨39, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (20681798701917 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101082357951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

end BstLean.Part268
