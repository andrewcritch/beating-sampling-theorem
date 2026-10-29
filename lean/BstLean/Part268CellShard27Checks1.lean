import BstLean.Part268CellShard27Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13025_20 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (20844521068633 / 25000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106617276399 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨20, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (20844521068633 / 25000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106617276399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_21 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41671842281649 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (553309639777 / 25000000000000 : ℝ))
      (E := (cell13025 ⟨21, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41671842281649 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (553309639777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_22 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83309308975581 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213242565619 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨22, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83309308975581 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213242565619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_23 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83274957478731 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106623287823 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨23, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83274957478731 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106623287823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_24 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (10405078755033 / 12500000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213250592269 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨24, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (10405078755033 / 12500000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213250592269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_25 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41603163313933 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106627279953 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨25, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41603163313933 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106627279953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_26 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (10396505901173 / 12500000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213258598001 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨26, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (10396505901173 / 12500000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213258598001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_27 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83137791752833 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276657824007 / 12500000000000 : ℝ))
      (E := (cell13025 ⟨27, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83137791752833 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276657824007 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_28 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (8310356022639 / 10000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213266602649 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨28, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (8310356022639 / 10000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213266602649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_29 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41534676299197 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106635315849 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨29, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41534676299197 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106635315849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_30 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41517584418673 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213274622351 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨30, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41517584418673 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213274622351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_31 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41500504455953 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276659829321 / 12500000000000 : ℝ))
      (E := (cell13025 ⟨31, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41500504455953 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276659829321 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_32 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (5185429549431 / 6250000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213282610991 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨32, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (5185429549431 / 6250000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213282610991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_33 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (16586552088659 / 20000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213286669787 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨33, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (16586552088659 / 20000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213286669787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_34 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41449335919119 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213290635899 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨34, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41449335919119 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213290635899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_35 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (82864606945019 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213294685727 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨35, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (82864606945019 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213294685727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_36 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41415282866543 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106649351153 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨36, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41415282866543 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106649351153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_37 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (82796548172043 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (27666283571 / 1250000000000 : ℝ))
      (E := (cell13025 ⟨37, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (82796548172043 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (27666283571 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_38 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41381277115823 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213306694399 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨38, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41381277115823 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213306694399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_39 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (20682145970451 / 25000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106655364067 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨39, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (20682145970451 / 25000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106655364067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13026_20 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (20844517504877 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213120851183 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨20, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (20844517504877 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213120851183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_21 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83343670314547 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (13832030333 / 625000000000 : ℝ))
      (E := (cell13026 ⟨21, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83343670314547 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (13832030333 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_22 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83309294733097 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (3541006169 / 160000000000 : ℝ))
      (E := (cell13026 ⟨22, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83309294733097 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (3541006169 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_23 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83274943242509 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213132861531 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨23, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83274943242509 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213132861531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_24 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83240615810299 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213136874081 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨24, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83240615810299 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213136874081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_25 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (10400789050519 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213140896117 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨25, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (10400789050519 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213140896117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_26 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (20793008247979 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442628986051 / 20000000000000 : ℝ))
      (E := (cell13026 ⟨26, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (20793008247979 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442628986051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_27 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41568888770803 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213148920399 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨27, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41568888770803 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213148920399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_28 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41551773010699 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276644115891 / 12500000000000 : ℝ))
      (E := (cell13026 ⟨28, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41551773010699 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276644115891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_29 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (5191833649977 / 6250000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213156952359 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨29, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (5191833649977 / 6250000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213156952359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_30 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83035154644809 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (55329023481 / 2500000000000 : ℝ))
      (E := (cell13026 ⟨30, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83035154644809 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (55329023481 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_31 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83000994725589 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213164947731 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨31, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83000994725589 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213164947731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_32 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41483429305397 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442633795813 / 20000000000000 : ℝ))
      (E := (cell13026 ⟨32, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41483429305397 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442633795813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_33 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82932746269401 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213172975639 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨33, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82932746269401 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213172975639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_34 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (20724664417637 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106588498401 / 50000000000000 : ℝ))
      (E := (cell13026 ⟨34, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (20724664417637 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106588498401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_35 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (10358074097941 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213180984451 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨35, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (10358074097941 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213180984451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_36 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82830551577789 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213184997537 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨36, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82830551577789 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213184997537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_37 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41398267011467 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (221318903617 / 10000000000000 : ℝ))
      (E := (cell13026 ⟨37, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41398267011467 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (221318903617 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_38 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (1034531751109 / 1250000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276649130189 / 12500000000000 : ℝ))
      (E := (cell13026 ⟨38, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (1034531751109 / 1250000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276649130189 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_39 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82728569745057 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213197013159 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨39, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82728569745057 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213197013159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13027_20 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (3335122230667 / 4000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213007203543 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨20, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (3335122230667 / 4000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213007203543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_21 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41671828033993 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (44260224029 / 2000000000000 : ℝ))
      (E := (cell13027 ⟨21, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41671828033993 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (44260224029 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_22 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83309280492803 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213015258009 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨22, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83309280492803 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213015258009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_23 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (3330997160339 / 4000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553254814961 / 25000000000000 : ℝ))
      (E := (cell13027 ⟨23, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (3330997160339 / 4000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553254814961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_24 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83240601582521 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213023268367 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨24, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83240601582521 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213023268367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_25 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (2600196818207 / 3125000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106513613999 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨25, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (2600196818207 / 3125000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106513613999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_26 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41586009388317 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106515629089 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨26, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41586009388317 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106515629089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_27 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83137763332563 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213035302887 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨27, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83137763332563 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213035302887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_28 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (8310353181859 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (88521572231 / 4000000000000 : ℝ))
      (E := (cell13027 ⟨28, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (8310353181859 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (88521572231 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_29 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83069324203053 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553260817173 / 25000000000000 : ℝ))
      (E := (cell13027 ⟨29, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83069324203053 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553260817173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_30 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41517570227227 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106523655173 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨30, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41517570227227 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106523655173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_31 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83000980541453 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442610263027 / 20000000000000 : ℝ))
      (E := (cell13027 ⟨31, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83000980541453 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442610263027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_32 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (8296684443287 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (69157979463 / 3125000000000 : ℝ))
      (E := (cell13027 ⟨32, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (8296684443287 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (69157979463 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_33 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41466366048843 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213059335781 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨33, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41466366048843 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213059335781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_34 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82898643505037 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (110653167669 / 5000000000000 : ℝ))
      (E := (cell13027 ⟨34, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82898643505037 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (110653167669 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_35 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41432289312107 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442613467503 / 20000000000000 : ℝ))
      (E := (cell13027 ⟨35, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41432289312107 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442613467503 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_36 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (20707634356167 / 25000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (221307134713 / 10000000000000 : ℝ))
      (E := (cell13027 ⟨36, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (20707634356167 / 25000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (221307134713 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_37 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82796519876001 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (110653769117 / 5000000000000 : ℝ))
      (E := (cell13027 ⟨37, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82796519876001 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (110653769117 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_38 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (8276252594797 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213079384303 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨38, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (8276252594797 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213079384303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_39 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (20682138902621 / 25000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (17704667291 / 800000000000 : ℝ))
      (E := (cell13027 ⟨39, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (20682138902621 / 25000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (17704667291 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13028_20 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83378041516033 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212893609877 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨20, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83378041516033 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212893609877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_21 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (16668728364723 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (110644880181 / 5000000000000 : ℝ))
      (E := (cell13028 ⟨21, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (16668728364723 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (110644880181 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_22 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83309266254697 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276612699713 / 12500000000000 : ℝ))
      (E := (cell13028 ⟨22, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83309266254697 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276612699713 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_23 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (8327491477663 / 10000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553226398861 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨23, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (8327491477663 / 10000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553226398861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_24 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83240587356931 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106454799959 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨24, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83240587356931 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106454799959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_25 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83206283963283 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106456806987 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨25, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83206283963283 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106456806987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_26 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (5198250285221 / 6250000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212917640223 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨26, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (5198250285221 / 6250000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212917640223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_27 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (16627549825141 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212921622571 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨27, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (16627549825141 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212921622571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_28 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (16620703523593 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106462840047 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨28, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (16620703523593 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106462840047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_29 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (5191831875541 / 6250000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212929697739 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨29, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (5191831875541 / 6250000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212929697739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_30 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (2075878156657 / 2500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106466838563 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨30, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (2075878156657 / 2500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106466838563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_31 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (10375120794937 / 12500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276617209777 / 12500000000000 : ℝ))
      (E := (cell13028 ⟨31, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (10375120794937 / 12500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276617209777 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_32 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82966830257127 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212941702241 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨32, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82966830257127 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212941702241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_33 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (1658654358563 / 2000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106472845799 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨33, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (1658654358563 / 2000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106472845799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_34 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41449314670851 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106474852819 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨34, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41449314670851 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106474852819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_35 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82864564467077 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212953744917 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨35, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82864564467077 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212953744917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_36 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41415261636861 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212957751087 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨36, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41415261636861 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212957751087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_37 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41398252865621 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (221296172419 / 10000000000000 : ℝ))
      (E := (cell13028 ⟨37, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41398252865621 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (221296172419 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_38 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (5172656988087 / 6250000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553241445377 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨38, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (5172656988087 / 6250000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553241445377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_39 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82728541478083 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106484873259 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨39, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82728541478083 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106484873259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13029_20 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41689013633791 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212780011877 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨20, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41689013633791 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212780011877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_21 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83343627581433 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212784001457 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨21, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83343627581433 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212784001457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_22 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (4165462600939 / 5000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (17287406183 / 781250000000 : ℝ))
      (E := (cell13029 ⟨22, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (4165462600939 / 5000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (17287406183 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_23 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (20818725136743 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212791985093 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨23, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (20818725136743 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212791985093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_24 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41620286566763 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553199010987 / 25000000000000 : ℝ))
      (E := (cell13029 ⟨24, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41620286566763 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553199010987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_25 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83206269746127 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212800054049 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨25, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83206269746127 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212800054049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_26 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (5198249397039 / 6250000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212804017939 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨26, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (5198249397039 / 6250000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212804017939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_27 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (8313773492103 / 10000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553202013719 / 25000000000000 : ℝ))
      (E := (cell13029 ⟨27, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (8313773492103 / 10000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553202013719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_28 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41551751709761 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212812050087 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨28, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41551751709761 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212812050087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_29 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83069295816441 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (110640803197 / 5000000000000 : ℝ))
      (E := (cell13029 ⟨29, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83069295816441 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (110640803197 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_30 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41517556040143 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106410049063 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨30, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41517556040143 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106410049063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_31 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (2075023804493 / 2500000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106412047769 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨31, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (2075023804493 / 2500000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106412047769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_32 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41483408041781 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442565623187 / 20000000000000 : ℝ))
      (E := (cell13029 ⟨32, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41483408041781 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442565623187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_33 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (82932703760791 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212832101709 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨33, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (82932703760791 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212832101709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_34 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (16579723036109 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (221283611221 / 10000000000000 : ℝ))
      (E := (cell13029 ⟨34, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (16579723036109 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (221283611221 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_35 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (20716137578029 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106420073999 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨35, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (20716137578029 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106420073999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_36 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (10353813640619 / 12500000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553211037681 / 25000000000000 : ℝ))
      (E := (cell13029 ⟨36, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (10353813640619 / 12500000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553211037681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_37 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (82796491588657 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212848179137 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨37, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (82796491588657 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212848179137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_38 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (20690624418247 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442570434879 / 20000000000000 : ℝ))
      (E := (cell13029 ⟨38, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (20690624418247 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442570434879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_39 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41364263673927 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106428097427 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨39, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41364263673927 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106428097427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13030_20 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (2084450325533 / 2500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106333204773 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨20, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (2084450325533 / 2500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106333204773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_21 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (83343613341441 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106335197481 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨21, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (83343613341441 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106335197481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_22 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (83309237785051 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (221267443917 / 10000000000000 : ℝ))
      (E := (cell13030 ⟨22, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (83309237785051 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (221267443917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_23 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (83274886319501 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (276584803599 / 12500000000000 : ℝ))
      (E := (cell13030 ⟨23, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (83274886319501 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (276584803599 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_24 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (20810139728077 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212682425243 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨24, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (20810139728077 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212682425243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_25 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (20801563882789 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (276585803921 / 12500000000000 : ℝ))
      (E := (cell13030 ⟨25, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (20801563882789 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (276585803921 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_26 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (16634395228779 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106345224889 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨26, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (16634395228779 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106345224889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_27 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (41568860359269 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (442538896571 / 20000000000000 : ℝ))
      (E := (cell13030 ⟨27, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (41568860359269 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (442538896571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_28 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (41551744611631 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553174618563 / 25000000000000 : ℝ))
      (E := (cell13030 ⟨28, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (41551744611631 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553174618563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_29 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (83069281626407 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (138293905271 / 6250000000000 : ℝ))
      (E := (cell13030 ⟨29, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (83069281626407 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (138293905271 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_30 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (83035097896473 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212706514801 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨30, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (83035097896473 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212706514801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_31 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (41500469001061 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212710508539 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨31, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (41500469001061 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212710508539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_32 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (3318672076487 / 4000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212714525307 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨32, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (3318672076487 / 4000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212714525307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_33 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (8293268959561 / 10000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106359253749 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨33, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (8293268959561 / 10000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106359253749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_34 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (20724650255391 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212722514463 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨34, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (20724650255391 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212722514463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_35 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82864536159329 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106363273381 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨35, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82864536159329 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106363273381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_36 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (20707623744589 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212730546043 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨36, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (20707623744589 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212730546043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_37 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (41398238724123 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106367285529 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨37, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (41398238724123 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106367285529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_38 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (20690620884689 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106369281483 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨38, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (20690620884689 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106369281483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_39 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82728513219797 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212742580119 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨39, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82728513219797 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212742580119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13031_20 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (2605562461789 / 3125000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212552861193 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨20, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (2605562461789 / 3125000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212552861193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_21 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (20835899775909 / 25000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (276569605309 / 12500000000000 : ℝ))
      (E := (cell13031 ⟨21, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (20835899775909 / 25000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (276569605309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_22 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83309223553509 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212560882587 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨22, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83309223553509 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212560882587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_23 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (10409359011777 / 12500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442512973633 / 20000000000000 : ℝ))
      (E := (cell13031 ⟨23, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (10409359011777 / 12500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442512973633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_24 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (3329621787731 / 4000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (276571107577 / 12500000000000 : ℝ))
      (E := (cell13031 ⟨24, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (3329621787731 / 4000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (276571107577 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_25 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (8320624131837 / 10000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442514584243 / 20000000000000 : ℝ))
      (E := (cell13031 ⟨25, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (8320624131837 / 10000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442514584243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_26 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (1663439238747 / 2000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212576935743 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨26, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (1663439238747 / 2000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212576935743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_27 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (20784426629557 / 25000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212580906511 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨27, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (20784426629557 / 25000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212580906511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_28 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83103475029183 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212584952591 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨28, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83103475029183 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212584952591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_29 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83069267438553 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553147239733 / 25000000000000 : ℝ))
      (E := (cell13031 ⟨29, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83069267438553 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553147239733 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_30 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (2075877092871 / 2500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442518585431 / 20000000000000 : ℝ))
      (E := (cell13031 ⟨30, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (2075877092871 / 2500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442518585431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_31 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (5187557739169 / 6250000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106298487893 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨31, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (5187557739169 / 6250000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106298487893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_32 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41483393871483 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (44252019779 / 2000000000000 : ℝ))
      (E := (cell13031 ⟨32, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41483393871483 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (44252019779 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_33 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (16586535086521 / 20000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212604967583 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨33, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (16586535086521 / 20000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212604967583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_34 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41449293432379 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212608971037 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨34, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41449293432379 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212608971037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_35 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41432261004359 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (221261299987 / 10000000000000 : ℝ))
      (E := (cell13031 ⟨35, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41432261004359 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (221261299987 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_36 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82830480833933 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553154248933 / 25000000000000 : ℝ))
      (E := (cell13031 ⟨36, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82830480833933 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553154248933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_37 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82796463310007 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106310508687 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨37, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82796463310007 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106310508687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_38 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (10345308675837 / 12500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106312502977 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨38, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (10345308675837 / 12500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106312502977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_39 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82728499093911 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106314509913 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨39, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82728499093911 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106314509913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13032_20 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (20844496133841 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221243930851 / 10000000000000 : ℝ))
      (E := (cell13032 ⟨20, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (20844496133841 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221243930851 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_21 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83343584868019 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (138277708999 / 6250000000000 : ℝ))
      (E := (cell13032 ⟨21, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83343584868019 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (138277708999 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_22 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (41654604662077 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (88497892867 / 4000000000000 : ℝ))
      (E := (cell13032 ⟨22, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (41654604662077 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (88497892867 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_23 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83274857871117 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553112840397 / 25000000000000 : ℝ))
      (E := (cell13032 ⟨23, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83274857871117 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553112840397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_24 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83240530476427 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442491070013 / 20000000000000 : ℝ))
      (E := (cell13032 ⟨24, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83240530476427 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442491070013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_25 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83206227107767 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212459348309 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨25, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83206227107767 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212459348309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_26 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83171947732987 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553115839733 / 25000000000000 : ℝ))
      (E := (cell13032 ⟨26, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83171947732987 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553115839733 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_27 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83137692320101 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106233692157 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨27, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83137692320101 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106233692157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_28 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (16620692167457 / 20000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553117842027 / 25000000000000 : ℝ))
      (E := (cell13032 ⟨28, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (16620692167457 / 20000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553117842027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_29 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (1038365665661 / 1250000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553118857301 / 25000000000000 : ℝ))
      (E := (cell13032 ⟨29, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (1038365665661 / 1250000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553118857301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_30 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (41517534767693 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221247939373 / 10000000000000 : ℝ))
      (E := (cell13032 ⟨30, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (41517534767693 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221247939373 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_31 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83000909653463 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212483438713 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨31, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83000909653463 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212483438713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_32 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (41483386787967 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (138280465517 / 6250000000000 : ℝ))
      (E := (cell13032 ⟨32, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (41483386787967 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (138280465517 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_33 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82932661271777 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553122855837 / 25000000000000 : ℝ))
      (E := (cell13032 ⟨33, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82932661271777 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553122855837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_34 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82898572710129 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (276561935241 / 12500000000000 : ℝ))
      (E := (cell13032 ⟨34, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82898572710129 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (276561935241 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_35 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (41432253930141 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106249724329 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨35, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (41432253930141 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106249724329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_36 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (16566093338337 / 20000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212503499787 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨36, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (16566093338337 / 20000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212503499787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_37 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82796449173941 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553126864843 / 25000000000000 : ℝ))
      (E := (cell13032 ⟨37, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82796449173941 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553126864843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_38 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (10345306909601 / 12500000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212511503357 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨38, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (10345306909601 / 12500000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212511503357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_39 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (16545696994039 / 20000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212515513973 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨39, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (16545696994039 / 20000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212515513973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13033_20 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83377970295669 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (138270363113 / 6250000000000 : ℝ))
      (E := (cell13033 ⟨20, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83377970295669 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (138270363113 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_21 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (8334357063459 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212329841169 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨21, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (8334357063459 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212329841169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_22 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (16661839019397 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212333814793 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨22, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (16661839019397 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212333814793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_23 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83274843650203 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212337850687 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨23, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83274843650203 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212337850687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_24 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83240516261763 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (221234183519 / 10000000000000 : ℝ))
      (E := (cell13033 ⟨24, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83240516261763 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (221234183519 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_25 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (20801553224837 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106172914753 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨25, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (20801553224837 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106172914753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_26 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83171933530807 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (276543729531 / 12500000000000 : ℝ))
      (E := (cell13033 ⟨26, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83171933530807 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (276543729531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_27 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (16627535624831 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442470771559 / 20000000000000 : ℝ))
      (E := (cell13033 ⟨27, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (16627535624831 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442470771559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_28 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (5193965415473 / 6250000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212357896299 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨28, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (5193965415473 / 6250000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212357896299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_29 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41534619534693 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553090473789 / 25000000000000 : ℝ))
      (E := (cell13033 ⟨29, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41534619534693 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553090473789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_30 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (8303505535811 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212365914531 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨30, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (8303505535811 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212365914531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_31 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83000895482401 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (55309247433 / 2500000000000 : ℝ))
      (E := (cell13033 ⟨31, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83000895482401 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (55309247433 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_32 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82966759411079 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212373903277 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨32, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82966759411079 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212373903277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_33 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (132692235381 / 160000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (221237793341 / 10000000000000 : ℝ))
      (E := (cell13033 ⟨33, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (132692235381 / 160000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (221237793341 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_34 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41449279278837 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106190964933 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨34, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41449279278837 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106190964933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_35 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82864493714019 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106192975897 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨35, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82864493714019 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106192975897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_36 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82830452551609 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212389940843 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨36, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82830452551609 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212389940843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_37 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82796435040047 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442478791153 / 20000000000000 : ℝ))
      (E := (cell13033 ⟨37, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82796435040047 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442478791153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_38 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82762441149091 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212397996449 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨38, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82762441149091 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212397996449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_39 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (1654569416973 / 2000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212402003809 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨39, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (1654569416973 / 2000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212402003809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13034_20 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83377956058161 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212212306777 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨20, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83377956058161 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212212306777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_21 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83343556403347 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106108167013 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨21, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83343556403347 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106108167013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_22 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (41654590436001 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212220361941 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨22, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (41654590436001 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212220361941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_23 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (3330993177259 / 4000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212224335457 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨23, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (3330993177259 / 4000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212224335457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_24 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (20810125512321 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212228374391 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨24, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (20810125512321 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212228374391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_25 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (10400774836639 / 12500000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (442446472961 / 20000000000000 : ℝ))
      (E := (cell13034 ⟨25, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (10400774836639 / 12500000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (442446472961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_26 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (8317191933081 / 10000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (221223636769 / 10000000000000 : ℝ))
      (E := (cell13034 ⟨26, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (8317191933081 / 10000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (221223636769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_27 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (8313766393039 / 10000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553060096357 / 25000000000000 : ℝ))
      (E := (cell13034 ⟨27, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (8313766393039 / 10000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553060096357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_28 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83103432460031 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212244420167 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨28, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83103432460031 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212244420167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_29 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (10383653111009 / 12500000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212248415307 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨29, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (10383653111009 / 12500000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212248415307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_30 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83035041183013 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212252431011 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨30, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83035041183013 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212252431011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_31 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (16600176262703 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (34566506409 / 1562500000000 : ℝ))
      (E := (cell13034 ⟨31, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (16600176262703 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (34566506409 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_32 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82966745248401 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106130206277 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨32, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82966745248401 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106130206277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_33 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (10366579119581 / 12500000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (442452887831 / 20000000000000 : ℝ))
      (E := (cell13034 ⟨33, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (10366579119581 / 12500000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (442452887831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_34 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82898544407393 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (17698147457 / 800000000000 : ℝ))
      (E := (cell13034 ⟨34, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82898544407393 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (17698147457 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_35 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82864479569929 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106136225307 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨35, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82864479569929 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106136225307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_36 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (41415219206853 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106138247477 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨36, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (41415219206853 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106138247477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_37 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (3311856836333 / 4000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212280506553 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨37, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (3311856836333 / 4000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212280506553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_38 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (16552485404709 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212284485227 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨38, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (16552485404709 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212284485227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_39 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (41364228364637 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553072122333 / 25000000000000 : ℝ))
      (E := (cell13034 ⟨39, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (41364228364637 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553072122333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13035_20 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83377941822841 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (221209885773 / 10000000000000 : ℝ))
      (E := (cell13035 ⟨20, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83377941822841 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (221209885773 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_21 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83343542174291 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (221210288089 / 10000000000000 : ℝ))
      (E := (cell13035 ⟨21, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83343542174291 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (221210288089 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_22 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (20827291662301 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212106846407 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨22, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (20827291662301 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212106846407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_23 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83274815214931 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (442422174857 / 20000000000000 : ℝ))
      (E := (cell13035 ⟨23, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83274815214931 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (442422174857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_24 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83240487838987 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212114909271 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨24, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83240487838987 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212114909271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_25 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41603092244529 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106059447891 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨25, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41603092244529 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106059447891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_26 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83171905132993 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553030723703 / 25000000000000 : ℝ))
      (E := (cell13035 ⟨26, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83171905132993 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553030723703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_27 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41568824869403 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (110606345437 / 5000000000000 : ℝ))
      (E := (cell13035 ⟨27, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41568824869403 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (110606345437 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_28 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41551709137337 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553032734929 / 25000000000000 : ℝ))
      (E := (cell13035 ⟨28, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41551709137337 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553032734929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_29 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (10383651338617 / 12500000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212134931139 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨29, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (10383651338617 / 12500000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212134931139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_30 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83035027010093 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106069471587 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨30, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83035027010093 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106069471587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_31 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83000867146807 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212142977281 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨31, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83000867146807 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212142977281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_32 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41483365543949 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106073488053 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨32, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41483365543949 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106073488053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_33 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41466309401173 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2765188749 / 125000000000 : ℝ))
      (E := (cell13035 ⟨33, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41466309401173 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2765188749 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_34 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41449265129643 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212154988709 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨34, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41449265129643 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212154988709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_35 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (82864465428013 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212159003781 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨35, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (82864465428013 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212159003781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_36 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41415212138987 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212162986069 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨36, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41415212138987 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212162986069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_37 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41398203389387 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553041763257 / 25000000000000 : ℝ))
      (E := (cell13035 ⟨37, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41398203389387 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553041763257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_38 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (10345301612521 / 12500000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106085514213 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨38, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (10345301612521 / 12500000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106085514213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_39 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (20682110653017 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212175029301 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨39, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (20682110653017 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212175029301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13036_20 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (83377927589707 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (552996351089 / 25000000000000 : ℝ))
      (E := (cell13036 ⟨20, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (83377927589707 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (552996351089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_21 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (83343527947421 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211989423429 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨21, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (83343527947421 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211989423429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_22 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (5206822026787 / 6250000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1105996721631 / 50000000000000 : ℝ))
      (E := (cell13036 ⟨22, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (5206822026787 / 6250000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1105996721631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_23 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (8327480100057 / 10000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (221199746717 / 10000000000000 : ℝ))
      (E := (cell13036 ⟨23, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (8327480100057 / 10000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (221199746717 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_24 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41620236815437 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (553000359957 / 25000000000000 : ℝ))
      (E := (cell13036 ⟨24, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41620236815437 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (553000359957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_25 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (83206170287187 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (442401096173 / 20000000000000 : ℝ))
      (E := (cell13036 ⟨25, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (83206170287187 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (442401096173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_26 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41585945468679 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212009476063 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨26, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41585945468679 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212009476063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_27 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41568817774701 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106006743103 / 50000000000000 : ℝ))
      (E := (cell13036 ⟨27, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41568817774701 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106006743103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_28 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (16620680818299 / 20000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (553004378361 / 25000000000000 : ℝ))
      (E := (cell13036 ⟨28, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (16620680818299 / 20000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (553004378361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_29 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41534598265989 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (88480860047 / 4000000000000 : ℝ))
      (E := (cell13036 ⟨29, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41534598265989 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (88480860047 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_30 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (1660700256787 / 2000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (553006377391 / 25000000000000 : ℝ))
      (E := (cell13036 ⟨30, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (1660700256787 / 2000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (553006377391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_31 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41500426491137 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (276503692509 / 12500000000000 : ℝ))
      (E := (cell13036 ⟨31, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41500426491137 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (276503692509 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_32 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (8296671692957 / 10000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212033535343 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨32, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (8296671692957 / 10000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212033535343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_33 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41466302325109 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (221203755493 / 10000000000000 : ℝ))
      (E := (cell13036 ⟨33, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41466302325109 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (221203755493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_34 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82898516113353 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212041540977 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨34, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82898516113353 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212041540977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_35 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82864451288269 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (553011388159 / 25000000000000 : ℝ))
      (E := (cell13036 ⟨35, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82864451288269 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (553011388159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_36 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41415205072207 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (13825309939 / 625000000000 : ℝ))
      (E := (cell13036 ⟨36, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41415205072207 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (13825309939 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_37 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82796392651393 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212053595193 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨37, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82796392651393 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212053595193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_38 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82762398778961 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (442411513463 / 20000000000000 : ℝ))
      (E := (cell13036 ⟨38, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82762398778961 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (442411513463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_39 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (8272842849703 / 10000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (442412324743 / 20000000000000 : ℝ))
      (E := (cell13036 ⟨39, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (8272842849703 / 10000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (442412324743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13037_20 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (2084447833969 / 2500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276484000621 / 12500000000000 : ℝ))
      (E := (cell13037 ⟨20, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (2084447833969 / 2500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276484000621 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_21 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (16668702744547 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211876019979 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨21, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (16668702744547 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211876019979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_22 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83309138210163 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552970008949 / 25000000000000 : ℝ))
      (E := (cell13037 ⟨22, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83309138210163 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552970008949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_23 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83274786788393 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211883997353 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨23, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83274786788393 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211883997353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_24 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83240459424943 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211888024467 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨24, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83240459424943 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211888024467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_25 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83206156087497 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211892061627 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨25, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83206156087497 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211892061627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_26 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83171876743903 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (442379210599 / 20000000000000 : ℝ))
      (E := (cell13037 ⟨26, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83171876743903 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (442379210599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_27 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83137621362177 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105950029677 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨27, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83137621362177 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105950029677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_28 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (16620677982099 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (442380816571 / 20000000000000 : ℝ))
      (E := (cell13037 ⟨28, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (16620677982099 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (442380816571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_29 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41534591178599 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105954033447 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨29, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41534591178599 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105954033447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_30 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (1297421854231 / 1562500000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105956035819 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨30, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (1297421854231 / 1562500000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105956035819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_31 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41500419409959 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211916098547 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨31, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41500419409959 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211916098547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_32 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82966702773417 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105960045133 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨32, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82966702773417 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105960045133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_33 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82932590500263 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211924106347 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨33, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82932590500263 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211924106347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_34 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (10362312746199 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211928147573 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨34, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (10362312746199 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211928147573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_35 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (10358054643837 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105966077921 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨35, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (10358054643837 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105966077921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_36 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (3313215840521 / 4000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211936131417 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨36, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (3313215840521 / 4000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211936131417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_37 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41398189263091 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211940191757 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨37, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41398189263091 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211940191757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_38 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (20690596164981 / 25000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211944160627 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨38, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (20690596164981 / 25000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211944160627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_39 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (517052589901 / 625000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105974106911 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨39, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (517052589901 / 625000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105974106911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13038_20 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41688949564999 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211758601257 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨20, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41688949564999 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211758601257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_21 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (16668699900047 / 20000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442352522441 / 20000000000000 : ℝ))
      (E := (cell13038 ⟨21, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (16668699900047 / 20000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442352522441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_22 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83309123993919 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105883312003 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨22, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83309123993919 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105883312003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_23 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83274772578399 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (88470825599 / 4000000000000 : ℝ))
      (E := (cell13038 ⟨23, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83274772578399 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (88470825599 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_24 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41620222610597 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211774663191 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨24, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41620222610597 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211774663191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_25 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83206141889987 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211778638071 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨25, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83206141889987 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211778638071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_26 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83171862552629 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (276472828201 / 12500000000000 : ℝ))
      (E := (cell13038 ⟨26, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83171862552629 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (276472828201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_27 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (20784401794283 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105893343329 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨27, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (20784401794283 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105893343329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_28 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41551687865837 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552947661987 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨28, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41551687865837 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552947661987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_29 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41534584092297 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211794686819 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨29, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41534584092297 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211794686819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_30 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (16606996900879 / 20000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211798687941 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨30, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (16606996900879 / 20000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211798687941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_31 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (10375103082467 / 12500000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552950677819 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨31, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (10375103082467 / 12500000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552950677819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_32 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82966688619439 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211806699467 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨32, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82966688619439 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211806699467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_33 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82932576352483 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105905356033 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨33, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82932576352483 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105905356033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_34 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (20724621957001 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211814749857 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨34, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (20724621957001 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211814749857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_35 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (647378304807 / 781250000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (138238672171 / 6250000000000 : ℝ))
      (E := (cell13038 ⟨35, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (647378304807 / 781250000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (138238672171 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_36 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82830381883807 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211822785653 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨36, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82830381883807 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211822785653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_37 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82796364403141 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552956696003 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨37, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82796364403141 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552956696003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_38 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41381185271527 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552957702091 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨38, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41381185271527 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552957702091 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_39 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82728400273457 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211834799623 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨39, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82728400273457 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211834799623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13039_20 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41688942451711 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105822625767 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨20, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41688942451711 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105822625767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_21 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83343485279919 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552912314611 / 25000000000000 : ℝ))
      (E := (cell13039 ⟨21, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83343485279919 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552912314611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_22 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83309109779857 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105826633127 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨22, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83309109779857 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105826633127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_23 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83274758370587 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105828639139 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨23, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83274758370587 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105828639139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_24 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41620215509813 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211661239191 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨24, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41620215509813 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211661239191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_25 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83206127694659 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211665268623 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨25, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83206127694659 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211665268623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_26 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83171848363533 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552917313089 / 25000000000000 : ℝ))
      (E := (cell13039 ⟨26, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83171848363533 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552917313089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_27 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (16627518598853 / 20000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211673309647 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨27, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (16627518598853 / 20000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211673309647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_28 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (8310336155503 / 10000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211677325721 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨28, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (8310336155503 / 10000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211677325721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_29 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (10383644251771 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552920325607 / 25000000000000 : ℝ))
      (E := (cell13039 ⟨29, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (10383644251771 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552920325607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_30 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83034970340181 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211685299931 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨30, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83034970340181 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211685299931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_31 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83000810501729 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211689319693 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨31, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83000810501729 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211689319693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_32 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41483337233817 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552923340737 / 25000000000000 : ℝ))
      (E := (cell13039 ⟨32, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41483337233817 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552923340737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_33 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (132692099531 / 160000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211697372089 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨33, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (132692099531 / 160000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211697372089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_34 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (20724618422147 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221170134783 / 10000000000000 : ℝ))
      (E := (cell13039 ⟨34, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (20724618422147 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221170134783 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_35 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41432204441033 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211705349321 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨35, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41432204441033 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211705349321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_36 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41415183878379 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211709376897 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨36, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41415183878379 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211709376897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_37 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (20699087570567 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (55292834299 / 2500000000000 : ℝ))
      (E := (cell13039 ⟨37, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (20699087570567 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (55292834299 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_38 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82762356428353 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105858696531 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨38, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82762356428353 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105858696531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_39 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41364193082461 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211721439873 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨39, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41364193082461 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211721439873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13040_20 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (8337787067903 / 10000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (138220743593 / 6250000000000 : ℝ))
      (E := (cell13040 ⟨20, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (8337787067903 / 10000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (138220743593 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_21 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83343471061787 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211535900361 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨21, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83343471061787 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211535900361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_22 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83309095567979 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211539904181 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨22, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83309095567979 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211539904181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_23 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83274744164957 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211543912261 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨23, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83274744164957 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211543912261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_24 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (1040505210253 / 1250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (3455543637 / 156250000000 : ℝ))
      (E := (cell13040 ⟨24, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (1040505210253 / 1250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (3455543637 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_25 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (8320611350151 / 10000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211551894857 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨25, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (8320611350151 / 10000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211551894857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_26 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83171834176617 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211555933237 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨26, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83171834176617 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211555933237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_27 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (10392197351697 / 12500000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211559928319 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨27, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (10392197351697 / 12500000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211559928319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_28 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83103347380563 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211563940681 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨28, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83103347380563 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211563940681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_29 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41534569922959 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552891993061 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨29, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41534569922959 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552891993061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_30 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41517478089071 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (276446495769 / 12500000000000 : ℝ))
      (E := (cell13040 ⟨30, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41517478089071 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (276446495769 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_31 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83000796345897 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552893995591 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨31, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83000796345897 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552893995591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_32 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82966660318003 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552894990881 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨32, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82966660318003 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552894990881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_33 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82932548063439 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105792013901 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨33, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82932548063439 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105792013901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_34 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82898459551343 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552897000033 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨34, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82898459551343 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552897000033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_35 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41432197375503 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (110579599913 / 5000000000000 : ℝ))
      (E := (cell13040 ⟨35, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41432197375503 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (110579599913 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_36 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82830353631879 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211596022517 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨36, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82830353631879 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211596022517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_37 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (16559267232713 / 20000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211600014307 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨37, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (16559267232713 / 20000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211600014307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_38 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82762342315819 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (442320806437 / 20000000000000 : ℝ))
      (E := (cell13040 ⟨38, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82762342315819 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (442320806437 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_39 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41364186029277 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (276451009477 / 12500000000000 : ℝ))
      (E := (cell13040 ⟨39, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41364186029277 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (276451009477 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13041_20 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83377856456823 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211418539121 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨20, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83377856456823 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211418539121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_21 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83343456845837 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211422537959 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨21, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83343456845837 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211422537959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_22 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83309081358283 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211426537789 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨22, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83309081358283 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211426537789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_23 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83274729961509 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105715270963 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨23, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83274729961509 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105715270963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_24 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83240402623033 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (44228691069 / 2000000000000 : ℝ))
      (E := (cell13041 ⟨24, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83240402623033 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (44228691069 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_25 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (4160304965527 / 5000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442287715041 / 20000000000000 : ℝ))
      (E := (cell13041 ⟨25, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (4160304965527 / 5000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442287715041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_26 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83171819991879 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211442609803 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨26, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83171819991879 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211442609803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_27 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (10392195579383 / 12500000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (34553853143 / 1562500000000 : ℝ))
      (E := (cell13041 ⟨27, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (10392195579383 / 12500000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (34553853143 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_28 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (5193958325517 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211450609827 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨28, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (5193958325517 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211450609827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_29 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83069125679843 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211454637749 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨29, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83069125679843 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211454637749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_30 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41517471009139 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211458628061 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨30, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41517471009139 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211458628061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_31 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41500391096119 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (88458505629 / 4000000000000 : ℝ))
      (E := (cell13041 ⟨31, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41500391096119 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (88458505629 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_32 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (5185415385659 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (138216667311 / 6250000000000 : ℝ))
      (E := (cell13041 ⟨32, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (5185415385659 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (138216667311 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_33 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (3317301356887 / 4000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105735339603 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨33, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (3317301356887 / 4000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105735339603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_34 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (20724611354067 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105737353383 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨34, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (20724611354067 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105737353383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_35 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82864380622117 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (138217418847 / 6250000000000 : ℝ))
      (E := (cell13041 ⟨35, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82864380622117 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (138217418847 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_36 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82830339509169 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552870680629 / 25000000000000 : ℝ))
      (E := (cell13041 ⟨36, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82830339509169 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552870680629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_37 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82796322047029 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (110574335553 / 5000000000000 : ℝ))
      (E := (cell13041 ⟨37, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82796322047029 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (110574335553 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_38 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82762328205453 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (276436340717 / 12500000000000 : ℝ))
      (E := (cell13041 ⟨38, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82762328205453 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (276436340717 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_39 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82728357954351 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211494766213 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨39, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82728357954351 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211494766213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13042_20 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83377842236799 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211305234747 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨20, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83377842236799 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211305234747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_21 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83343442632071 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552827307393 / 25000000000000 : ℝ))
      (E := (cell13042 ⟨21, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83343442632071 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552827307393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_22 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83309067150769 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552828306359 / 25000000000000 : ℝ))
      (E := (cell13042 ⟨22, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83309067150769 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552828306359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_23 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83274715760241 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211317284037 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨23, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83274715760241 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211317284037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_24 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83240388428007 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211321291711 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨24, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83240388428007 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211321291711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_25 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (332824340487 / 400000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442265050247 / 20000000000000 : ℝ))
      (E := (cell13042 ⟨25, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (332824340487 / 400000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442265050247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_26 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83171805809319 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (276416160257 / 12500000000000 : ℝ))
      (E := (cell13042 ⟨26, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83171805809319 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (276416160257 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_27 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (8313755045873 / 10000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442266665629 / 20000000000000 : ℝ))
      (E := (cell13042 ⟨27, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (8313755045873 / 10000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442266665629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_28 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41551659519079 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105668666579 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨28, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41551659519079 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105668666579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_29 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83069111515943 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211341298941 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨29, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83069111515943 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211341298941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_30 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (20758731965147 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442269068841 / 20000000000000 : ℝ))
      (E := (cell13042 ⟨30, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (20758731965147 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442269068841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_31 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (5187548002547 / 6250000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105674676673 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨31, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (5187548002547 / 6250000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105674676673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_32 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82966632025257 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105676663763 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨32, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82966632025257 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105676663763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_33 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82932519783083 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552839346229 / 25000000000000 : ℝ))
      (E := (cell13042 ⟨33, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82932519783083 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552839346229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_34 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (16579686256673 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552840337613 / 25000000000000 : ℝ))
      (E := (cell13042 ⟨34, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (16579686256673 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552840337613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_35 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82864366495397 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211365400539 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨35, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82864366495397 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211365400539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_36 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (20707581347157 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (221136941821 / 10000000000000 : ℝ))
      (E := (cell13042 ⟨36, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (20707581347157 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (221136941821 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_37 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82796307932661 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211373403507 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨37, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82796307932661 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211373403507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_38 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82762314097253 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211377414983 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨38, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82762314097253 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211377414983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_39 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41364171926157 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211381452307 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨39, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41364171926157 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211381452307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13043_20 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83377828018959 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552797981513 / 25000000000000 : ℝ))
      (E := (cell13043 ⟨20, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83377828018959 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552797981513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_21 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83343428420487 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105597987601 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨21, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83343428420487 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105597987601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_22 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (20827263236359 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (17689599737 / 800000000000 : ℝ))
      (E := (cell13043 ⟨22, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (20827263236359 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (17689599737 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_23 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41637350780577 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211203963449 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨23, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41637350780577 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211203963449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_24 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (2081009355879 / 2500000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552801991813 / 25000000000000 : ℝ))
      (E := (cell13043 ⟨24, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (2081009355879 / 2500000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552801991813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_25 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41603035467569 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (110560599069 / 5000000000000 : ℝ))
      (E := (cell13043 ⟨25, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41603035467569 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (110560599069 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_26 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83171791628937 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (442243201689 / 20000000000000 : ℝ))
      (E := (cell13043 ⟨26, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83171791628937 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (442243201689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_27 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (20784384071143 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (69100624761 / 3125000000000 : ℝ))
      (E := (cell13043 ⟨27, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (20784384071143 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (69100624761 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_28 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83103304870219 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211224052177 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨28, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83103304870219 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211224052177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_29 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41534548677109 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (442245602869 / 20000000000000 : ℝ))
      (E := (cell13043 ⟨29, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41534548677109 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (442245602869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_30 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83034913705071 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211232056039 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨30, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83034913705071 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211232056039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_31 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83000753891439 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (276404507707 / 12500000000000 : ℝ))
      (E := (cell13043 ⟨31, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83000753891439 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (276404507707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_32 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41483308941071 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (276405011369 / 12500000000000 : ℝ))
      (E := (cell13043 ⟨32, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41483308941071 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (276405011369 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_33 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82932505646161 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211244086319 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨33, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82932505646161 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211244086319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_34 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82898417152631 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (221124810711 / 10000000000000 : ℝ))
      (E := (cell13043 ⟨34, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82898417152631 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (221124810711 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_35 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (16572870474169 / 20000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211252095221 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨35, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (16572870474169 / 20000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211252095221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_36 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41415155635127 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2764070137 / 125000000000 : ℝ))
      (E := (cell13043 ⟨36, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41415155635127 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2764070137 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_37 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82796293820459 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211260150361 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨37, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82796293820459 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211260150361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_38 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82762299991219 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (110563207933 / 5000000000000 : ℝ))
      (E := (cell13043 ⟨38, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82762299991219 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (110563207933 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_39 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82728329752443 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211268134097 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨39, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82728329752443 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211268134097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13044_20 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (83377813803301 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276384833919 / 12500000000000 : ℝ))
      (E := (cell13044 ⟨20, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (83377813803301 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276384833919 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_21 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (16668682842217 / 20000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442216543303 / 20000000000000 : ℝ))
      (E := (cell13044 ⟨21, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (16668682842217 / 20000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442216543303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_22 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (83309038742283 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211086704499 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨22, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (83309038742283 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211086704499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_23 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41637343682123 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211090696929 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨23, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41637343682123 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211090696929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_24 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (20810090011123 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442218939377 / 20000000000000 : ℝ))
      (E := (cell13044 ⟨24, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (20810090011123 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442218939377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_25 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (5200378546919 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552774676803 / 25000000000000 : ℝ))
      (E := (cell13044 ⟨25, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (5200378546919 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552774676803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_26 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (20792944362683 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105551365261 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨26, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (20792944362683 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105551365261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_27 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (8313752211259 / 10000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211106769197 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨27, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (8313752211259 / 10000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211106769197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_28 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (16620658140891 / 20000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105555383443 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨28, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (16620658140891 / 20000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105555383443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_29 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (20767270798667 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211114783959 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨29, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (20767270798667 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211114783959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_30 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (5189681221983 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552779690891 / 25000000000000 : ℝ))
      (E := (cell13044 ⟨30, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (5189681221983 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552779690891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_31 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41500369872149 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552780706057 / 25000000000000 : ℝ))
      (E := (cell13044 ⟨31, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41500369872149 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552780706057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_32 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82966603741199 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211126791479 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨32, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82966603741199 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211126791479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_33 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82932491511409 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211130842033 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨33, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82932491511409 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211130842033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_34 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41449201512033 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276391850103 / 12500000000000 : ℝ))
      (E := (cell13044 ⟨34, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41449201512033 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276391850103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_35 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82864338248463 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211138844259 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨35, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82864338248463 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211138844259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_36 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (161777924129 / 195312500000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211142855371 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨36, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (161777924129 / 195312500000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211142855371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_37 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (3311851188417 / 4000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211146834201 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨37, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (3311851188417 / 4000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211146834201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_38 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82762285887351 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442230179607 / 20000000000000 : ℝ))
      (E := (cell13044 ⟨38, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82762285887351 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442230179607 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_39 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (5170519728421 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211154870343 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨39, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (5170519728421 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211154870343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13045_20 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41688899794913 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105482735323 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨20, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41688899794913 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105482735323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_21 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (10417925000483 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (276371181689 / 12500000000000 : ℝ))
      (E := (cell13045 ⟨21, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (10417925000483 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (276371181689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_22 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (650851754229 / 781250000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552743359389 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨22, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (650851754229 / 781250000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552743359389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_23 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41637336584759 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552744371119 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨23, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41637336584759 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552744371119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_24 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41620172928001 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210981480609 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨24, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41620172928001 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210981480609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_25 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83206042568447 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (55274637179 / 2500000000000 : ℝ))
      (E := (cell13045 ⟨25, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83206042568447 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (55274637179 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_26 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83171763274703 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (110549475337 / 5000000000000 : ℝ))
      (E := (cell13045 ⟨26, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83171763274703 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (110549475337 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_27 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83137507942783 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552748385433 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨27, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83137507942783 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552748385433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_28 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41551638270433 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210997535783 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨28, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41551638270433 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210997535783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_29 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (8306906903729 / 10000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211001549267 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨29, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (8306906903729 / 10000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211001549267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_30 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41517442700279 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105502762663 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨30, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41517442700279 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105502762663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_31 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83000725599329 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552752395623 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨31, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83000725599329 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552752395623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_32 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41483294801213 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552753386573 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨32, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41483294801213 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552753386573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_33 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20733119344707 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (13818859959 / 625000000000 : ℝ))
      (E := (cell13045 ⟨33, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20733119344707 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (13818859959 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_34 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (8289838889767 / 10000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (276377700939 / 12500000000000 : ℝ))
      (E := (cell13045 ⟨34, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (8289838889767 / 10000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (276377700939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_35 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (10358040516031 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (442205117799 / 20000000000000 : ℝ))
      (E := (cell13045 ⟨35, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (10358040516031 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (442205117799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_36 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (10353785380001 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211029596841 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨36, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (10353785380001 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211029596841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_37 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20699066400639 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (55275840779 / 2500000000000 : ℝ))
      (E := (cell13045 ⟨37, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20699066400639 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (55275840779 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_38 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (82762271785647 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (221103763311 / 10000000000000 : ℝ))
      (E := (cell13045 ⟨38, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (82762271785647 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (221103763311 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_39 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (82728301559193 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105520830523 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨39, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (82728301559193 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105520830523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13046_20 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (20844446344633 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105426103657 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨20, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (20844446344633 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105426103657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_21 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (10417923224853 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210856244529 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨21, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (10417923224853 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210856244529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_22 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (2082725258563 / 2500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105430112329 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨22, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (2082725258563 / 2500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105430112329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_23 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83274658976969 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221086426771 / 10000000000000 : ℝ))
      (E := (cell13046 ⟨23, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83274658976969 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221086426771 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_24 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (8324033166969 / 10000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210868260021 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨24, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (8324033166969 / 10000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210868260021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_25 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83206028388367 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210872262797 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨25, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83206028388367 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210872262797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_26 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (1663434982017 / 2000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (276359534831 / 12500000000000 : ℝ))
      (E := (cell13046 ⟨26, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (1663434982017 / 2000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (276359534831 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_27 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (5196093360947 / 6250000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210880309957 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨27, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (5196093360947 / 6250000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210880309957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_28 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83103262379451 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (552721075093 / 25000000000000 : ℝ))
      (E := (cell13046 ⟨28, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83103262379451 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (552721075093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_29 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (41534527441043 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105444155133 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨29, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (41534527441043 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105444155133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_30 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83034871251559 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (138180771333 / 6250000000000 : ℝ))
      (E := (cell13046 ⟨30, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83034871251559 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (138180771333 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_31 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83000711456531 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210896336451 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨31, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83000711456531 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210896336451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_32 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (2592705483307 / 3125000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (34545318053 / 1562500000000 : ℝ))
      (E := (cell13046 ⟨32, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (2592705483307 / 3125000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (34545318053 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_33 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (16586492649683 / 20000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (34545380321 / 1562500000000 : ℝ))
      (E := (cell13046 ⟨33, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (16586492649683 / 20000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (34545380321 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_34 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82898374773443 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210908351257 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨34, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82898374773443 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210908351257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_35 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (414321550051 / 500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210912388091 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨35, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (414321550051 / 500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210912388091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_36 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (10353783616017 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105458196347 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨36, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (10353783616017 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105458196347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_37 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82796251496853 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210920423817 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨37, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82796251496853 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210920423817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_38 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82762257686109 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105462211309 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨38, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82762257686109 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105462211309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_39 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82728287465813 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210928447451 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨39, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82728287465813 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210928447451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13047_20 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83377771169419 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (221073905629 / 10000000000000 : ℝ))
      (E := (cell13047 ⟨20, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83377771169419 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (221073905629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_21 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (20835842898991 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210743031233 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨21, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (20835842898991 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210743031233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_22 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83308996145907 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210747065807 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨22, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83308996145907 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210747065807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_23 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41637322393299 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (276343880829 / 12500000000000 : ℝ))
      (E := (cell13047 ⟨23, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41637322393299 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (276343880829 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_24 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (20810079371389 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210755093527 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨24, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (20810079371389 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210755093527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_25 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (2600187944077 / 3125000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (276344886569 / 12500000000000 : ℝ))
      (E := (cell13047 ⟨25, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (2600187944077 / 3125000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (276344886569 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_26 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83171734929173 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105381552349 / 50000000000000 : ℝ))
      (E := (cell13047 ⟨26, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83171734929173 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105381552349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_27 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (16627495921939 / 20000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210767073873 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨27, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (16627495921939 / 20000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210767073873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_28 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83103248220209 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210771119153 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨28, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83103248220209 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210771119153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_29 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (16613808145811 / 20000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (55269378137 / 2500000000000 : ℝ))
      (E := (cell13047 ⟨29, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (16613808145811 / 20000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (55269378137 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_30 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83034857104733 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210779153023 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨30, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83034857104733 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210779153023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_31 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (1296885895561 / 1562500000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105391572337 / 50000000000000 : ℝ))
      (E := (cell13047 ⟨31, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (1296885895561 / 1562500000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105391572337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_32 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (82966561331391 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210787160189 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨32, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (82966561331391 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210787160189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_33 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (20733112280043 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (55269778549 / 2500000000000 : ℝ))
      (E := (cell13047 ⟨33, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (20733112280043 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (55269778549 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_34 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (10362295081423 / 12500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210795149339 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨34, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (10362295081423 / 12500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210795149339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_35 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (1035803698679 / 1250000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105399591443 / 50000000000000 : ℝ))
      (E := (cell13047 ⟨35, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (1035803698679 / 1250000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105399591443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_36 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (82830254818429 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210803184247 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨36, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (82830254818429 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210803184247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_37 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41398118696657 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (138175450761 / 6250000000000 : ℝ))
      (E := (cell13047 ⟨37, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41398118696657 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (138175450761 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_38 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41381121794367 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210811207827 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨38, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41381121794367 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210811207827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_39 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (82728273374597 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210815229557 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨39, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (82728273374597 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210815229557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13048_20 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (10422219620311 / 12500000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (27632823033 / 1250000000000 : ℝ))
      (E := (cell13048 ⟨20, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (10422219620311 / 12500000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (27632823033 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_21 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (20835839348821 / 25000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210629871959 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨21, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (20835839348821 / 25000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210629871959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_22 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83308981951473 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210633902643 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨22, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83308981951473 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210633902643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_23 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (16654926119681 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (17685103037 / 800000000000 : ℝ))
      (E := (cell13048 ⟨23, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (16654926119681 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (17685103037 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_24 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (41620151651799 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552660480681 / 25000000000000 : ℝ))
      (E := (cell13048 ⟨24, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (41620151651799 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552660480681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_25 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83206000034737 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105322958999 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨25, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83206000034737 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105322958999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_26 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (8317172075967 / 10000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210649926441 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨26, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (8317172075967 / 10000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210649926441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_27 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (20784366361603 / 25000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105326975217 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨27, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (20784366361603 / 25000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105326975217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_28 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83103234063141 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105328966813 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨28, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83103234063141 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105328966813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_29 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (16613805315639 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210661936391 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨29, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (16613805315639 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210661936391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_30 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83034842960077 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (442133192083 / 20000000000000 : ℝ))
      (E := (cell13048 ⟨30, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83034842960077 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (442133192083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_31 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83000683177447 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105334974297 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨31, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83000683177447 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105334974297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_32 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (10370818399891 / 12500000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105336980341 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨32, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (10370818399891 / 12500000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105336980341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_33 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82932434994097 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (221067799769 / 10000000000000 : ℝ))
      (E := (cell13048 ⟨33, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82932434994097 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (221067799769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_34 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82898346531491 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210682001761 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨34, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82898346531491 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210682001761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_35 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (16572856356121 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552671508011 / 25000000000000 : ℝ))
      (E := (cell13048 ⟨35, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (16572856356121 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552671508011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_36 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82830240710887 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552672507547 / 25000000000000 : ℝ))
      (E := (cell13048 ⟨36, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82830240710887 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552672507547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_37 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82796223291941 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (442138810989 / 20000000000000 : ℝ))
      (E := (cell13048 ⟨37, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82796223291941 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (442138810989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_38 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82762229493523 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (138168627967 / 6250000000000 : ℝ))
      (E := (cell13048 ⟨38, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82762229493523 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (138168627967 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_39 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (10341032410693 / 12500000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210702066123 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨39, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (10341032410693 / 12500000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210702066123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13049_20 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (10422217844717 / 12500000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (221051268299 / 10000000000000 : ℝ))
      (E := (cell13049 ⟨20, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (10422217844717 / 12500000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (221051268299 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_21 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83343343196783 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210516708373 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨21, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83343343196783 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210516708373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_22 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83308967759217 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210520735169 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨22, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83308967759217 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210520735169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_23 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83274616412389 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552631177077 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨23, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83274616412389 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552631177077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_24 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83240289123817 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210528747611 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨24, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83240289123817 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210528747611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_25 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (16641197172237 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (442106547827 / 20000000000000 : ℝ))
      (E := (cell13049 ⟨25, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (16641197172237 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (442106547827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_26 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41585853296171 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552634185969 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨26, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41585853296171 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552634185969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_27 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83137451285303 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552635191053 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨27, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83137451285303 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552635191053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_28 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (16620643981649 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210544802293 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨28, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (16620643981649 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210544802293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_29 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83069012429507 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210548801517 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨29, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83069012429507 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210548801517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_30 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (10379353602199 / 12500000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (69079775689 / 3125000000000 : ℝ))
      (E := (cell13049 ⟨30, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (10379353602199 / 12500000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (69079775689 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_31 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (2075016726029 / 2500000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210556806779 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨31, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (2075016726029 / 2500000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210556806779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_32 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82966533069033 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105280407733 / 50000000000000 : ℝ))
      (E := (cell13049 ⟨32, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82966533069033 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105280407733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_33 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82932420870189 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210564849119 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨33, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82932420870189 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210564849119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_34 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41449166206883 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210568849881 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨34, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41449166206883 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210568849881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_35 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82864267669057 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210572876901 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨35, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82864267669057 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210572876901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_36 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82830226605511 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210576871829 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨36, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82830226605511 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210576871829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_37 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82796209192731 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210580893417 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨37, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82796209192731 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210580893417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_38 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (3310488616019 / 4000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210584882819 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨38, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (3310488616019 / 4000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210584882819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_39 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (20682061299663 / 25000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105294449197 / 50000000000000 : ℝ))
      (E := (cell13049 ⟨39, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (20682061299663 / 25000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105294449197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

end BstLean.Part268
