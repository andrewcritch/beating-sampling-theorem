import BstLean.Part263Shard3Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12300_20 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83384846325573 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (115209465743 / 5000000000000 : ℝ))
      (E := (cell12300 ⟨20, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83384846325573 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (115209465743 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_21 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41675117852649 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576048319449 / 25000000000000 : ℝ))
      (E := (cell12300 ⟨21, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41675117852649 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576048319449 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_22 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20828912375663 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304197271683 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨22, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20828912375663 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304197271683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_23 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83281087684393 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152100650517 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨23, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83281087684393 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152100650517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_24 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20811637554363 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304205311793 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨24, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20811637554363 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304205311793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_25 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (8321203706893 / 10000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576052326981 / 25000000000000 : ℝ))
      (E := (cell12300 ⟨25, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (8321203706893 / 10000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576052326981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_26 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41588774103049 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576053323289 / 25000000000000 : ℝ))
      (E := (cell12300 ⟨26, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41588774103049 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576053323289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_27 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41571541798197 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304217270983 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨27, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41571541798197 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304217270983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_28 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (3324345728297 / 4000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304221244663 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨28, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (3324345728297 / 4000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304221244663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_29 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83074227006963 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576056318917 / 25000000000000 : ℝ))
      (E := (cell12300 ⟨29, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83074227006963 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576056318917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_30 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (16607966992589 / 20000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152114624959 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨30, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (16607966992589 / 20000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152114624959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_31 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (3320218681739 / 4000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460846645679 / 20000000000000 : ℝ))
      (E := (cell12300 ⟨31, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (3320218681739 / 4000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460846645679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_32 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (5185695201051 / 6250000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (46084745439 / 2000000000000 : ℝ))
      (E := (cell12300 ⟨32, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (5185695201051 / 6250000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (46084745439 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_33 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20734200862849 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304241265667 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨33, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20734200862849 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304241265667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_34 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20725626928951 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460849042269 / 20000000000000 : ℝ))
      (E := (cell12300 ⟨34, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20725626928951 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460849042269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_35 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20717058994697 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460849845547 / 20000000000000 : ℝ))
      (E := (cell12300 ⟨35, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20717058994697 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460849845547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_36 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (82833988209257 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (288031649887 / 12500000000000 : ℝ))
      (E := (cell12300 ⟨36, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (82833988209257 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (288031649887 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_37 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20699941094069 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (115212862191 / 5000000000000 : ℝ))
      (E := (cell12300 ⟨37, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20699941094069 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (115212862191 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_38 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (8276556444907 / 10000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304261186961 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨38, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (8276556444907 / 10000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304261186961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_39 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (82731388397019 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152132602583 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨39, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (82731388397019 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152132602583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12301_20 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83384836832289 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152023083647 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨20, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83384836832289 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152023083647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_21 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83350226538939 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576012536003 / 25000000000000 : ℝ))
      (E := (cell12301 ⟨21, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83350226538939 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576012536003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_22 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83315640662761 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (115202707623 / 5000000000000 : ℝ))
      (E := (cell12301 ⟨22, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83315640662761 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (115202707623 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_23 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (5205067448157 / 6250000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460811627769 / 20000000000000 : ℝ))
      (E := (cell12301 ⟨23, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (5205067448157 / 6250000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460811627769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_24 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83246542029127 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (36000971339 / 1562500000000 : ℝ))
      (E := (cell12301 ⟨24, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83246542029127 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (36000971339 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_25 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (16642405841141 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460813224069 / 20000000000000 : ℝ))
      (E := (cell12301 ⟨25, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (16642405841141 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460813224069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_26 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83177540667519 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304070123201 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨26, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83177540667519 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304070123201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_27 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83143076382009 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304074119427 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨27, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83143076382009 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304074119427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_28 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41554318158391 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304078112279 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨28, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41554318158391 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304078112279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_29 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (8307422043961 / 10000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304082104783 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨29, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (8307422043961 / 10000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304082104783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_30 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83039828718433 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144005381233 / 6250000000000 : ℝ))
      (E := (cell12301 ⟨30, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83039828718433 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144005381233 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_31 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83005461121353 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152045049837 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨31, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83005461121353 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152045049837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_32 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (20742779404159 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304094106949 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨32, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (20742779404159 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304094106949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_33 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (8293679817271 / 10000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304098065109 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨33, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (8293679817271 / 10000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304098065109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_34 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41451251379083 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576025523271 / 25000000000000 : ℝ))
      (E := (cell12301 ⟨34, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41451251379083 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576025523271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_35 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (10358528917719 / 12500000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304106075407 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨35, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (10358528917719 / 12500000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304106075407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_36 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82833983892377 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576027518009 / 25000000000000 : ℝ))
      (E := (cell12301 ⟨36, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82833983892377 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576027518009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_37 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82799760379109 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304114084157 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨37, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82799760379109 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304114084157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_38 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82765560771171 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (92164722163 / 4000000000000 : ℝ))
      (E := (cell12301 ⟨38, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82765560771171 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (92164722163 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_39 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41365692518973 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152061020569 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨39, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41365692518973 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152061020569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12302_20 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (83384827340797 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303903073549 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨20, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (83384827340797 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303903073549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_21 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (20837554343583 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303907064113 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨21, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (20837554343583 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303907064113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_22 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (83315631824579 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303911087189 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨22, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (83315631824579 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303911087189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_23 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (83281070658301 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151957544489 / 50000000000000 : ℝ))
      (E := (cell12302 ⟨23, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (83281070658301 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151957544489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_24 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (8324653384243 / 10000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303919073683 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨24, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (8324653384243 / 10000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303919073683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_25 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (20803005336017 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303923045267 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨25, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (20803005336017 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303923045267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_26 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (10397191641311 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (575981766459 / 25000000000000 : ℝ))
      (E := (cell12302 ⟨26, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (10397191641311 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (575981766459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_27 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (83143069169131 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (46078621611 / 2000000000000 : ℝ))
      (E := (cell12302 ⟨27, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (83143069169131 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (46078621611 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_28 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (20777157356901 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (3599898491 / 156250000000 : ℝ))
      (E := (cell12302 ⟨28, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (20777157356901 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (3599898491 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_29 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41537106936841 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (575984761689 / 25000000000000 : ℝ))
      (E := (cell12302 ⟨29, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41537106936841 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (575984761689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_30 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (16607964495061 / 20000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (460788612497 / 20000000000000 : ℝ))
      (E := (cell12302 ⟨30, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (16607964495061 / 20000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (460788612497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_31 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (3320218208023 / 4000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (575986756373 / 25000000000000 : ℝ))
      (E := (cell12302 ⟨31, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (3320218208023 / 4000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (575986756373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_32 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (518569450111 / 625000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (230395105507 / 10000000000000 : ℝ))
      (E := (cell12302 ⟨32, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (518569450111 / 625000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (230395105507 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_33 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82936792895289 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303955036303 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨33, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82936792895289 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303955036303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_34 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (10362812225219 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (460791805911 / 20000000000000 : ℝ))
      (E := (cell12302 ⟨34, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (10362812225219 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (460791805911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_35 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82868226705899 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303963036467 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨35, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82868226705899 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303963036467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_36 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82833979576641 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151983499919 / 50000000000000 : ℝ))
      (E := (cell12302 ⟨36, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82833979576641 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151983499919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_37 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (16559951276609 / 20000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303970979421 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨37, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (16559951276609 / 20000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303970979421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_38 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (1293211829599 / 1562500000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (115198748809 / 5000000000000 : ℝ))
      (E := (cell12302 ⟨38, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (1293211829599 / 1562500000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (115198748809 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_39 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (10341422709987 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303978990851 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨39, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (10341422709987 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303978990851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12303_20 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83384817851097 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151880045931 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨20, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83384817851097 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151880045931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_21 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (3334008328459 / 4000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151882048181 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨21, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (3334008328459 / 4000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151882048181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_22 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (20828905747027 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230376807587 / 10000000000000 : ℝ))
      (E := (cell12303 ⟨22, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (20828905747027 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230376807587 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_23 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83281062147759 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230377209313 / 10000000000000 : ℝ))
      (E := (cell12303 ⟨23, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83281062147759 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230377209313 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_24 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83246525657361 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (575944023521 / 25000000000000 : ℝ))
      (E := (cell12303 ⟨24, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83246525657361 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (575944023521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_25 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41606006742009 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151890041347 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨25, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41606006742009 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151890041347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_26 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (20794381398751 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151892031343 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨26, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (20794381398751 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151892031343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_27 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83143061957759 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303788037551 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨27, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83143061957759 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303788037551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_28 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83108622539893 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303792068969 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨28, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83108622539893 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303792068969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_29 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (4153710365459 / 5000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303796043137 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨29, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (4153710365459 / 5000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303796043137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_30 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41519908116781 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (575950005311 / 25000000000000 : ℝ))
      (E := (cell12303 ⟨30, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41519908116781 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (575950005311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_31 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41502724640571 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (287975508043 / 12500000000000 : ℝ))
      (E := (cell12303 ⟨31, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41502724640571 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (287975508043 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_32 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82971106420189 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460761611559 / 20000000000000 : ℝ))
      (E := (cell12303 ⟨32, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82971106420189 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460761611559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_33 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82936787619131 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (18430496029 / 800000000000 : ℝ))
      (E := (cell12303 ⟨33, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82936787619131 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (18430496029 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_34 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82902492846561 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151908010381 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨34, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82902492846561 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151908010381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_35 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (8286822207123 / 10000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (287977499217 / 12500000000000 : ℝ))
      (E := (cell12303 ⟨35, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (8286822207123 / 10000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (287977499217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_36 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (2588561726939 / 3125000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303824041117 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨36, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (2588561726939 / 3125000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303824041117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_37 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (20699938097021 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303827988251 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨37, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (20699938097021 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303827988251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_38 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (20691388354641 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303832011939 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨38, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (20691388354641 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303832011939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_39 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82731378322871 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303835995621 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨39, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82731378322871 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303835995621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12304_20 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83384808363189 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303617163997 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨20, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83384808363189 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303617163997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_21 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83350199050369 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (921448473 / 40000000000 : ℝ))
      (E := (cell12304 ⟨21, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83350199050369 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (921448473 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_22 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83315614153347 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575906294197 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨22, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83315614153347 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575906294197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_23 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41640526819443 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303629151301 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨23, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41640526819443 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303629151301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_24 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83246517473921 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303633168569 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨24, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83246517473921 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303633168569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_25 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (20803001406389 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (230363717427 / 10000000000000 : ℝ))
      (E := (cell12304 ⟨25, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (20803001406389 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (230363717427 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_26 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41588759030533 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303641172129 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨26, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41588759030533 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303641172129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_27 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83143054747893 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575911291409 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨27, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83143054747893 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575911291409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_28 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41554307826823 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151824579023 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨28, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41554307826823 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151824579023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_29 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83074200746103 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151826576189 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨29, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83074200746103 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151826576189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_30 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83039809993203 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (35994642991 / 1562500000000 : ℝ))
      (E := (cell12304 ⟨30, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83039809993203 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (35994642991 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_31 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83005443363053 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151830549621 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨31, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83005443363053 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151830549621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_32 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (82971100823921 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303665115127 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨32, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (82971100823921 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303665115127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_33 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (82936782344237 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (56241921 / 2441406250 : ℝ))
      (E := (cell12304 ⟨33, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (82936782344237 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (56241921 / 2441406250 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_34 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41451243946297 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303673125269 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨34, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41451243946297 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303673125269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_35 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (5179263589859 / 6250000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (460735424597 / 20000000000000 : ℝ))
      (E := (cell12304 ⟨35, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (5179263589859 / 6250000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (460735424597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_36 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41416985474299 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (287960134831 / 12500000000000 : ℝ))
      (E := (cell12304 ⟨36, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41416985474299 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (287960134831 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_37 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41399874197113 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303685110647 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨37, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41399874197113 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303685110647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_38 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (16553109948771 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575922275673 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨38, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (16553109948771 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575922275673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_39 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (20682843741717 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303693114133 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨39, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (20682843741717 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303693114133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12305_20 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (5211549929817 / 6250000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460694869639 / 20000000000000 : ℝ))
      (E := (cell12305 ⟨20, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (5211549929817 / 6250000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460694869639 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_21 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (83350189891013 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (71983697579 / 3125000000000 : ℝ))
      (E := (cell12305 ⟨21, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (83350189891013 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (71983697579 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_22 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41657802660147 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (143967645729 / 6250000000000 : ℝ))
      (E := (cell12305 ⟨22, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41657802660147 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (143967645729 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_23 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (83281045131681 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151743160901 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨23, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (83281045131681 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151743160901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_24 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (83246509292107 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303490297143 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨24, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (83246509292107 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303490297143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_25 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (2080299944217 / 2500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (28793679 / 1250000000 : ℝ))
      (E := (cell12305 ⟨25, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (2080299944217 / 2500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (28793679 / 1250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_26 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41588755264337 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (575874569353 / 25000000000000 : ℝ))
      (E := (cell12305 ⟨26, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41588755264337 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (575874569353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_27 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (20785761884883 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151751144801 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨27, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (20785761884883 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151751144801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_28 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (16621721753773 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303506301469 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨28, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (16621721753773 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303506301469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_29 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (1661483883689 / 2000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303510316033 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨29, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (1661483883689 / 2000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303510316033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_30 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (83039803754229 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303514277609 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨30, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (83039803754229 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303514277609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_31 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (20751359361577 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (92140732227 / 4000000000000 : ℝ))
      (E := (cell12305 ⟨31, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (20751359361577 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (92140732227 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_32 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (20742773807239 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303522285587 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨32, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (20742773807239 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303522285587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_33 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41468388535303 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303526277911 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨33, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41468388535303 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303526277911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_34 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (1658049658797 / 2000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460706056903 / 20000000000000 : ℝ))
      (E := (cell12305 ⟨34, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (1658049658797 / 2000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460706056903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_35 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82868212805441 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151767124223 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨35, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82868212805441 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151767124223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_36 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82833966636291 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303538229659 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨36, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82833966636291 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303538229659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_37 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82799744401471 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151771114669 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨37, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82799744401471 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151771114669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_38 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82765546070209 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151773124221 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨38, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82765546070209 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151773124221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_39 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (5170710725743 / 6250000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (71985944657 / 3125000000000 : ℝ))
      (E := (cell12305 ⟨39, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (5170710725743 / 6250000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (71985944657 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12306_20 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41692394696373 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303331586219 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨20, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41692394696373 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303331586219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_21 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41675090366703 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230333557471 / 10000000000000 : ℝ))
      (E := (cell12306 ⟨21, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41675090366703 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230333557471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_22 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (1666311929779 / 2000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151669770249 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨22, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (1666311929779 / 2000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151669770249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_23 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83281036626143 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303343546327 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨23, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83281036626143 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303343546327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_24 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83246501111921 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460669507627 / 20000000000000 : ℝ))
      (E := (cell12306 ⟨24, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83246501111921 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460669507627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_25 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83211989913391 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151675759941 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨25, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83211989913391 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151675759941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_26 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20794375749457 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303355553671 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨26, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20794375749457 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303355553671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_27 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20785760083169 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460671905251 / 20000000000000 : ℝ))
      (E := (cell12306 ⟨27, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20785760083169 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460671905251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_28 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20777150471387 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575840889417 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨28, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20777150471387 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575840889417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_29 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83074187624221 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303367534103 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨29, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83074187624221 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303367534103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_30 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41519898758319 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303371516747 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨30, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41519898758319 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303371516747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_31 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41502715765453 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575843877039 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨31, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41502715765453 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575843877039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_32 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (16594217927059 / 20000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151689755327 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨32, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (16594217927059 / 20000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151689755327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_33 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41468385899119 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (35990367599 / 1562500000000 : ℝ))
      (E := (cell12306 ⟨33, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41468385899119 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (35990367599 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_34 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (10362809748541 / 12500000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (4606774997 / 200000000000 : ℝ))
      (E := (cell12306 ⟨34, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (10362809748541 / 12500000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (4606774997 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_35 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (1035852602179 / 1250000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151695743651 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨35, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (1035852602179 / 1250000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151695743651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_36 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41416981162563 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303395494153 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨36, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41416981162563 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303395494153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_37 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41399870204909 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303399461599 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨37, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41399870204909 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303399461599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_38 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (662124339181 / 800000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (46068070157 / 2000000000000 : ℝ))
      (E := (cell12306 ⟨38, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (662124339181 / 800000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (46068070157 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_39 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82731368257931 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303407457659 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨39, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82731368257931 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303407457659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12307_20 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (8338477991021 / 10000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303188878071 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨20, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (8338477991021 / 10000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303188878071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_21 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (83350171577549 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460638576157 / 20000000000000 : ℝ))
      (E := (cell12307 ⟨21, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (83350171577549 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460638576157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_22 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (16663117531863 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151598430787 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨22, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (16663117531863 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151598430787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_23 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41640514061137 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303200883183 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨23, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41640514061137 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303200883183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_24 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41623246466681 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151602416609 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨24, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41623246466681 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151602416609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_25 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (83211982059687 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575802208069 / 25000000000000 : ℝ))
      (E := (cell12307 ⟨25, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (83211982059687 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575802208069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_26 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (83177495468527 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575803206443 / 25000000000000 : ℝ))
      (E := (cell12307 ⟨26, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (83177495468527 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575803206443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_27 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (3325721325093 / 4000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151608408597 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨27, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (3325721325093 / 4000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151608408597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_28 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (5194287187731 / 6250000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (35987825153 / 1562500000000 : ℝ))
      (E := (cell12307 ⟨28, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (5194287187731 / 6250000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (35987825153 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_29 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (10384272633177 / 12500000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575806201647 / 25000000000000 : ℝ))
      (E := (cell12307 ⟨29, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (10384272633177 / 12500000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575806201647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_30 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (8303979128043 / 10000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151614405183 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨30, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (8303979128043 / 10000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151614405183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_31 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41502712808423 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (3598801287 / 156250000000 : ℝ))
      (E := (cell12307 ⟨31, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41502712808423 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (3598801287 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_32 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (10371385505367 / 12500000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151618395167 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨32, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (10371385505367 / 12500000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151618395167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_33 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (20734191631783 / 25000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303240829437 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨33, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (20734191631783 / 25000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303240829437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_34 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (20725618259507 / 25000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (35988200403 / 1562500000000 : ℝ))
      (E := (cell12307 ⟨34, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (20725618259507 / 25000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (35988200403 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_35 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82868203544381 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151624390481 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨35, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82868203544381 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151624390481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_36 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82833958015103 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575813203379 / 25000000000000 : ℝ))
      (E := (cell12307 ⟨36, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82833958015103 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575813203379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_37 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82799736419267 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (287907100929 / 12500000000000 : ℝ))
      (E := (cell12307 ⟨37, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82799736419267 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (287907100929 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_38 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82765538726103 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303260763597 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨38, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82765538726103 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303260763597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_39 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (16546272980999 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303264800043 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨39, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (16546272980999 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303264800043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12308_20 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83384770429463 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303046281991 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨20, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83384770429463 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303046281991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_21 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (1041877030293 / 1250000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460610048151 / 20000000000000 : ℝ))
      (E := (cell12308 ⟨21, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (1041877030293 / 1250000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460610048151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_22 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83315578831387 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303054236611 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨22, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83315578831387 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303054236611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_23 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83281019620071 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151529137033 / 50000000000000 : ℝ))
      (E := (cell12308 ⟨23, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83281019620071 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151529137033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_24 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83246484756429 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303062240723 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨24, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83246484756429 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303062240723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_25 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (8321197420757 / 10000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (115153312859 / 5000000000000 : ℝ))
      (E := (cell12308 ⟨25, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (8321197420757 / 10000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (115153312859 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_26 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83177487940771 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (287883776309 / 12500000000000 : ℝ))
      (E := (cell12308 ⟨26, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83177487940771 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (287883776309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_27 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83143025923479 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (115153711041 / 5000000000000 : ℝ))
      (E := (cell12308 ⟨27, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83143025923479 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (115153711041 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_28 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83108588123307 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303078233119 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨28, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83108588123307 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303078233119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_29 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41537087254017 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303082191939 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨29, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41537087254017 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303082191939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_30 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (16607957009121 / 20000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303086216939 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨30, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (16607957009121 / 20000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303086216939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_31 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83005419704129 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303090193751 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨31, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83005419704129 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303090193751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_32 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (82971078451879 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460618836629 / 20000000000000 : ℝ))
      (E := (cell12308 ⟨32, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (82971078451879 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460618836629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_33 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (82936761257287 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (143943636701 / 6250000000000 : ℝ))
      (E := (cell12308 ⟨33, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (82936761257287 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (143943636701 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_34 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (82902468088951 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (92124088313 / 4000000000000 : ℝ))
      (E := (cell12308 ⟨34, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (82902468088951 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (92124088313 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_35 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (10358524864453 / 12500000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303106188019 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨35, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (10358524864453 / 12500000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303106188019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_36 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41416976853111 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (9212440751 / 400000000000 : ℝ))
      (E := (cell12308 ⟨36, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41416976853111 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (9212440751 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_37 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41399866214909 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (11515571041 / 500000000000 : ℝ))
      (E := (cell12308 ⟨37, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41399866214909 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (11515571041 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_38 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (82765535055643 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (143944886979 / 6250000000000 : ℝ))
      (E := (cell12308 ⟨38, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (82765535055643 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (143944886979 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_39 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41365680776541 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303122197491 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨39, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41365680776541 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303122197491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12309_20 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (41692380475253 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (115145186987 / 5000000000000 : ℝ))
      (E := (cell12309 ⟨20, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (41692380475253 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (115145186987 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_21 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (2083753831777 / 2500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302907712881 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨21, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (2083753831777 / 2500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302907712881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_22 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83315570005167 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151455861947 / 50000000000000 : ℝ))
      (E := (cell12309 ⟨22, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83315570005167 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151455861947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_23 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (16656202223907 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151457859487 / 50000000000000 : ℝ))
      (E := (cell12309 ⟨23, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (16656202223907 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151457859487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_24 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83246476581121 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (28786496279 / 1250000000000 : ℝ))
      (E := (cell12309 ⟨24, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83246476581121 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (28786496279 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_25 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83211966357037 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151461838943 / 50000000000000 : ℝ))
      (E := (cell12309 ⟨25, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83211966357037 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151461838943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_26 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83177480414559 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (92117108311 / 4000000000000 : ℝ))
      (E := (cell12309 ⟨26, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83177480414559 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (92117108311 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_27 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (5196438670071 / 6250000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460586335747 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨27, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (5196438670071 / 6250000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460586335747 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_28 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83108581244381 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151467826187 / 50000000000000 : ℝ))
      (E := (cell12309 ⟨28, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83108581244381 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151467826187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_29 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (3322966718083 / 4000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151469845079 / 50000000000000 : ℝ))
      (E := (cell12309 ⟨29, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (3322966718083 / 4000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151469845079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_30 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83039778812163 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460588735599 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨30, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83039778812163 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460588735599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_31 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (16601082758551 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460589535373 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨31, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (16601082758551 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460589535373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_32 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (20742768215531 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (17991810071 / 781250000000 : ℝ))
      (E := (cell12309 ⟨32, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (20742768215531 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (17991810071 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_33 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (16587351197741 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151477829107 / 50000000000000 : ℝ))
      (E := (cell12309 ⟨33, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (16587351197741 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151477829107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_34 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (41451231570547 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302959644601 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨34, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (41451231570547 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302959644601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_35 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (5179262143003 / 6250000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302963649883 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨35, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (5179262143003 / 6250000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302963649883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_36 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (41416974699241 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287870952107 / 12500000000000 : ℝ))
      (E := (cell12309 ⟨36, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (41416974699241 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287870952107 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_37 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (8279972844147 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460594332781 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨37, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (8279972844147 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460594332781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_38 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (20691382846561 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287871952009 / 12500000000000 : ℝ))
      (E := (cell12309 ⟨38, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (20691382846561 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287871952009 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_39 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (8273135820219 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460595930001 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨39, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (8273135820219 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460595930001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12310_20 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83384751473337 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151380625661 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨20, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83384751473337 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151380625661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_21 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83350144120467 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151382619453 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨21, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83350144120467 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151382619453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_22 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41657780590327 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (115138463257 / 5000000000000 : ℝ))
      (E := (cell12310 ⟨22, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41657780590327 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (115138463257 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_23 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (10410125327583 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151386608957 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨23, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (10410125327583 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151386608957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_24 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83246468407439 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575694304503 / 25000000000000 : ℝ))
      (E := (cell12310 ⟨24, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83246468407439 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575694304503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_25 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83211958508089 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575695302777 / 25000000000000 : ℝ))
      (E := (cell12310 ⟨25, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83211958508089 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575695302777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_26 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (20794368222473 / 25000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302785200923 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨26, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (20794368222473 / 25000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302785200923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_27 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83143011520297 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (115139459547 / 5000000000000 : ℝ))
      (E := (cell12310 ⟨27, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83143011520297 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (115139459547 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_28 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41554287183459 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (230279318441 / 10000000000000 : ℝ))
      (E := (cell12310 ⟨28, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41554287183459 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (230279318441 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_29 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41537080698769 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575699296087 / 25000000000000 : ℝ))
      (E := (cell12310 ⟨29, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41537080698769 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575699296087 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_30 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41519886290051 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151400596769 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨30, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41519886290051 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151400596769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_31 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41502703941361 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (230280521453 / 10000000000000 : ℝ))
      (E := (cell12310 ⟨31, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41502703941361 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (230280521453 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_32 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (8297106727367 / 10000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (287851148891 / 12500000000000 : ℝ))
      (E := (cell12310 ⟨32, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (8297106727367 / 10000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (287851148891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_33 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (10367093840173 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575703295973 / 25000000000000 : ℝ))
      (E := (cell12310 ⟨33, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (10367093840173 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575703295973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_34 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82902458194459 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (35981518667 / 1562500000000 : ℝ))
      (E := (cell12310 ⟨34, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82902458194459 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (35981518667 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_35 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82868189661653 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302821166557 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨35, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82868189661653 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302821166557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_36 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82833945091883 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (46056503189 / 2000000000000 : ℝ))
      (E := (cell12310 ⟨36, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82833945091883 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (46056503189 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_37 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (5174982778389 / 6250000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302829174547 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨37, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (5174982778389 / 6250000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302829174547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_38 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41382763858953 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (460566630829 / 20000000000000 : ℝ))
      (E := (cell12310 ⟨38, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41382763858953 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (460566630829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_39 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82731354852319 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151418578793 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨39, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82731354852319 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151418578793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12311_20 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (83384741997957 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (92104754999 / 4000000000000 : ℝ))
      (E := (cell12311 ⟨20, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (83384741997957 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (92104754999 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_21 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41675067485801 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302622877091 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨21, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41675067485801 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302622877091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_22 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (83315552357847 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302626860351 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨22, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (83315552357847 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302626860351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_23 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (4164049706173 / 5000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (230263082919 / 10000000000000 : ℝ))
      (E := (cell12311 ⟨23, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (4164049706173 / 5000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (230263082919 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_24 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41623230117691 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302634846131 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨24, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41623230117691 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302634846131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_25 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (3328478026429 / 4000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151319428423 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨25, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (3328478026429 / 4000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151319428423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_26 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (5198591585423 / 6250000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575660701669 / 25000000000000 : ℝ))
      (E := (cell12311 ⟨26, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (5198591585423 / 6250000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575660701669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_27 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (259821888503 / 312500000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302646815839 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨27, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (259821888503 / 312500000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302646815839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_28 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41554283745459 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575662707307 / 25000000000000 : ℝ))
      (E := (cell12311 ⟨28, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41554283745459 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575662707307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_29 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (83074154844423 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302654791409 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨29, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (83074154844423 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302654791409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_30 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (5189985396839 / 6250000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151329411019 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨30, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (5189985396839 / 6250000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151329411019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_31 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (8300540197403 / 10000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302662806747 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨31, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (8300540197403 / 10000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302662806747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_32 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41485530843259 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151333403151 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨32, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41485530843259 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151333403151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_33 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82936745455323 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575667705699 / 25000000000000 : ℝ))
      (E := (cell12311 ⟨33, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82936745455323 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575667705699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_34 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (20725613312261 / 25000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151337399761 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨34, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (20725613312261 / 25000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151337399761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_35 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82868185036439 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (287834849579 / 12500000000000 : ℝ))
      (E := (cell12311 ⟨35, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82868185036439 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (287834849579 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_36 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (3313357631457 / 4000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302682756919 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨36, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (3313357631457 / 4000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302682756919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_37 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41399860234039 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302686798767 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨37, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41399860234039 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302686798767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_38 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82765524050629 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151345402941 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨38, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82765524050629 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151345402941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_39 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (8273135150347 / 10000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (57567369473 / 2500000000000 : ℝ))
      (E := (cell12311 ⟨39, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (8273135150347 / 10000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (57567369473 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12312_20 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20846183131091 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460495310493 / 20000000000000 : ℝ))
      (E := (cell12312 ⟨20, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20846183131091 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460495310493 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_21 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20837531456121 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151240284589 / 50000000000000 : ℝ))
      (E := (cell12312 ⟨21, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20837531456121 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151240284589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_22 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (41657771768373 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (230248450953 / 10000000000000 : ℝ))
      (E := (cell12312 ⟨22, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (41657771768373 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (230248450953 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_23 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83280985627921 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302488552807 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨23, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83280985627921 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302488552807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_24 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83246452064949 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575623132087 / 25000000000000 : ℝ))
      (E := (cell12312 ⟨24, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83246452064949 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575623132087 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_25 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (2600373212967 / 3125000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (287812062299 / 12500000000000 : ℝ))
      (E := (cell12312 ⟨25, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (2600373212967 / 3125000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (287812062299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_26 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83177457845187 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302500525037 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨26, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83177457845187 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302500525037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_27 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (41571498561563 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302504495031 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨27, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (41571498561563 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302504495031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_28 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (4155428030819 / 5000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575627132101 / 25000000000000 : ℝ))
      (E := (cell12312 ⟨28, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (4155428030819 / 5000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575627132101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_29 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83074148292731 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302512511341 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨29, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83074148292731 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302512511341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_30 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (41519880060063 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575629126257 / 25000000000000 : ℝ))
      (E := (cell12312 ⟨30, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (41519880060063 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575629126257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_31 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (2075134901667 / 2500000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575630128003 / 25000000000000 : ℝ))
      (E := (cell12312 ⟨31, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (2075134901667 / 2500000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575630128003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_32 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (41485528050333 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (35976944939 / 1562500000000 : ℝ))
      (E := (cell12312 ⟨32, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (41485528050333 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (35976944939 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_33 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20734185047631 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151264228919 / 50000000000000 : ℝ))
      (E := (cell12312 ⟨33, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20734185047631 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151264228919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_34 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (1658048966097 / 2000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151266229551 / 50000000000000 : ℝ))
      (E := (cell12312 ⟨34, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (1658048966097 / 2000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151266229551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_35 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (16573636082481 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302536481519 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨35, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (16573636082481 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302536481519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_36 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (82833936482107 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302540467879 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨36, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (82833936482107 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302540467879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_37 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (10349964560379 / 12500000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302544477929 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨37, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (10349964560379 / 12500000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302544477929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_38 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (82765520384413 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575637113491 / 25000000000000 : ℝ))
      (E := (cell12312 ⟨38, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (82765520384413 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575637113491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_39 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (82731348155641 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575638113831 / 25000000000000 : ℝ))
      (E := (cell12312 ⟨39, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (82731348155641 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (575638113831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12313_20 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83384723052559 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302334283791 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨20, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83384723052559 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302334283791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_21 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (10418764584889 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151169157583 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨21, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (10418764584889 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151169157583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_22 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83315534717351 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (28779278387 / 1250000000000 : ℝ))
      (E := (cell12313 ⟨22, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83315534717351 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (28779278387 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_23 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (41640488567023 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302346272149 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨23, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (41640488567023 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302346272149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_24 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83246443896141 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151175132331 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨24, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83246443896141 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151175132331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_25 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (20802983742687 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287794281557 / 12500000000000 : ℝ))
      (E := (cell12313 ⟨25, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (20802983742687 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287794281557 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_26 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83177450325149 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151179148813 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨26, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83177450325149 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151179148813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_27 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (16628597985359 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302362286919 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨27, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (16628597985359 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302362286919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_28 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (10388569217913 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302366281939 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨28, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (10388569217913 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302366281939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_29 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83074141742459 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302370227249 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨29, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83074141742459 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302370227249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_30 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (8303975389221 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151187121253 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨30, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (8303975389221 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151187121253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_31 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (8300539016067 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287797283979 / 12500000000000 : ℝ))
      (E := (cell12313 ⟨31, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (8300539016067 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287797283979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_32 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (16594210103223 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302382259027 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨32, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (16594210103223 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302382259027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_33 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (10367091865873 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302386264651 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨33, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (10367091865873 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302386264651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_34 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (20725610840469 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151195115999 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨34, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (20725610840469 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151195115999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_35 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (5179260986847 / 6250000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302394221217 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨35, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (5179260986847 / 6250000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302394221217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_36 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (82833932178929 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575599558429 / 25000000000000 : ℝ))
      (E := (cell12313 ⟨36, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (82833932178929 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575599558429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_37 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (41399856249543 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302402212033 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨37, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (41399856249543 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302402212033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_38 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (82765516719257 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302406215713 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨38, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (82765516719257 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302406215713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_39 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (646338631319 / 781250000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (5756025467 / 250000000000 : ℝ))
      (E := (cell12313 ⟨39, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (646338631319 / 781250000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (5756025467 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12314_20 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (4169235679127 / 5000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302192127193 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨20, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (4169235679127 / 5000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302192127193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_21 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41675053767743 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151098057529 / 50000000000000 : ℝ))
      (E := (cell12314 ⟨21, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41675053767743 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151098057529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_22 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (4165776294983 / 5000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460440028929 / 20000000000000 : ℝ))
      (E := (cell12314 ⟨22, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (4165776294983 / 5000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460440028929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_23 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (20820242160459 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (287775512979 / 12500000000000 : ℝ))
      (E := (cell12314 ⟨23, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (20820242160459 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (287775512979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_24 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (20811608932239 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (8993000443 / 390625000000 : ℝ))
      (E := (cell12314 ⟨24, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (20811608932239 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (8993000443 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_25 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41605963564067 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (899301609 / 39062500000 : ℝ))
      (E := (cell12314 ⟨25, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41605963564067 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (899301609 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_26 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (83177442806653 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460443224889 / 20000000000000 : ℝ))
      (E := (cell12314 ⟨26, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (83177442806653 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460443224889 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_27 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (16628596546393 / 20000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (23022200747 / 1000000000000 : ℝ))
      (E := (cell12314 ⟨27, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (16628596546393 / 20000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (23022200747 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_28 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (83108546871689 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302224089833 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨28, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (83108546871689 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302224089833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_29 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (10384266899201 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302228114481 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨29, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (10384266899201 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302228114481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_30 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41519873832837 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302232092947 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨30, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41519873832837 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302232092947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_31 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (1296959129 / 1562500000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302236086207 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨31, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (1296959129 / 1562500000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302236086207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_32 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (324105644269 / 390625000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151120048289 / 50000000000000 : ℝ))
      (E := (cell12314 ⟨32, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (324105644269 / 390625000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151120048289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_33 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (1295886401011 / 1562500000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460448813521 / 20000000000000 : ℝ))
      (E := (cell12314 ⟨33, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (1295886401011 / 1562500000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460448813521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_34 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41451219210061 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302248059643 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨34, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41451219210061 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302248059643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_35 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41434085583939 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302252074321 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨35, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41434085583939 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302252074321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_36 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (82833927876891 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (71945501701 / 3125000000000 : ℝ))
      (E := (cell12314 ⟨36, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (82833927876891 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (71945501701 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_37 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (1034996356453 / 1250000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151130029859 / 50000000000000 : ℝ))
      (E := (cell12314 ⟨37, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (1034996356453 / 1250000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151130029859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_38 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (82765513055161 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (230226403247 / 10000000000000 : ℝ))
      (E := (cell12314 ⟨38, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (82765513055161 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (230226403247 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_39 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (20682835365761 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302268032031 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨39, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (20682835365761 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302268032031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12315_20 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20846176028577 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151025012217 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨20, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20846176028577 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151025012217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_21 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (16670019678721 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151027013559 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨21, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (16670019678721 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151027013559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_22 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (3332620683347 / 4000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151029007007 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨22, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (3332620683347 / 4000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151029007007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_23 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (8328096015129 / 10000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302062047861 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨23, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (8328096015129 / 10000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302062047861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_24 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41623213781697 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (140506959 / 6103515625 : ℝ))
      (E := (cell12315 ⟨24, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41623213781697 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (140506959 / 6103515625 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_25 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41605959643551 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143879377487 / 6250000000000 : ℝ))
      (E := (cell12315 ⟨25, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41605959643551 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143879377487 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_26 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83177435289699 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (287759250687 / 12500000000000 : ℝ))
      (E := (cell12315 ⟨26, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83177435289699 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (287759250687 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_27 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83142975538637 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (115103898759 / 5000000000000 : ℝ))
      (E := (cell12315 ⟨27, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83142975538637 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (115103898759 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_28 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (16621708000307 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302082010517 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨28, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (16621708000307 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302082010517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_29 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41537064323089 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (230208599769 / 10000000000000 : ℝ))
      (E := (cell12315 ⟨29, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41537064323089 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (230208599769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_30 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83039741440519 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (57552249947 / 2500000000000 : ℝ))
      (E := (cell12315 ⟨30, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83039741440519 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (57552249947 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_31 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83005378352671 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151046977569 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨31, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83005378352671 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151046977569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_32 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (648211244929 / 781250000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143881124297 / 6250000000000 : ℝ))
      (E := (cell12315 ⟨32, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (648211244929 / 781250000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143881124297 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_33 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20734181100921 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (230210198379 / 10000000000000 : ℝ))
      (E := (cell12315 ⟨33, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20734181100921 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (230210198379 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_34 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (82902433479587 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302105942039 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨34, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (82902433479587 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302105942039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_35 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (82868166547383 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151054991121 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨35, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (82868166547383 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151054991121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_36 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (10354240446999 / 12500000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302113988643 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨36, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (10354240446999 / 12500000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302113988643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_37 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41399852267247 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302117962347 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨37, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41399852267247 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302117962347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_38 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20691377348031 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151060981449 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨38, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20691377348031 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151060981449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_39 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (3309253524731 / 4000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302125932337 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨39, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (3309253524731 / 4000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302125932337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12316_20 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41692347323931 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575477008439 / 25000000000000 : ℝ))
      (E := (cell12316 ⟨20, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41692347323931 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575477008439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_21 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (8335008925347 / 10000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301911993083 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨21, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (8335008925347 / 10000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301911993083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_22 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41657754134697 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301915995641 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨22, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41657754134697 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301915995641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_23 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (83280951662407 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (115095999381 / 5000000000000 : ℝ))
      (E := (cell12316 ⟨23, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (83280951662407 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (115095999381 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_24 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (16649283879891 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301923973207 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨24, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (16649283879891 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301923973207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_25 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (83211911447653 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (287741001839 / 12500000000000 : ℝ))
      (E := (cell12316 ⟨25, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (83211911447653 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (287741001839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_26 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (83177427774287 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301931999159 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨26, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (83177427774287 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301931999159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_27 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (8314296834681 / 10000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301935988361 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨27, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (8314296834681 / 10000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301935988361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_28 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (83108533132841 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (460387997113 / 20000000000000 : ℝ))
      (E := (cell12316 ⟨28, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (83108533132841 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (460387997113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_29 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (10384265262521 / 12500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150971996889 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨29, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (10384265262521 / 12500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150971996889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_30 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (83039735216743 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301947957307 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨30, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (83039735216743 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301947957307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_31 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (2075134311267 / 2500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150975968563 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨31, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (2075134311267 / 2500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150975968563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_32 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (4148551688513 / 5000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301955935549 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨32, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (4148551688513 / 5000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301955935549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_33 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82936719143923 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150979977331 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨33, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82936719143923 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150979977331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_34 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82902428540271 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575490984439 / 25000000000000 : ℝ))
      (E := (cell12316 ⟨34, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82902428540271 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575490984439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_35 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82868161928067 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (115098397249 / 5000000000000 : ℝ))
      (E := (cell12316 ⟨35, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82868161928067 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (115098397249 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_36 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (10354239909529 / 12500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301971919121 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨36, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (10354239909529 / 12500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301971919121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_37 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41399850276923 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301975919923 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨37, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41399850276923 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301975919923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_38 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41382752865073 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301979948337 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨38, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41382752865073 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301979948337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_39 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (3309253390981 / 4000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575495986601 / 25000000000000 : ℝ))
      (E := (cell12316 ⟨39, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (3309253390981 / 4000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575495986601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12317_20 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83384685183201 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (57544152423 / 2500000000000 : ℝ))
      (E := (cell12317 ⟨20, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83384685183201 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (57544152423 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_21 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83350080115079 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (115088503561 / 5000000000000 : ℝ))
      (E := (cell12317 ⟨21, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83350080115079 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (115088503561 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_22 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (5207218716051 / 6250000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301774031243 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨22, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (5207218716051 / 6250000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301774031243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_23 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83280943175187 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150889019863 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨23, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83280943175187 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150889019863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_24 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41623205618569 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460356408519 / 20000000000000 : ℝ))
      (E := (cell12317 ⟨24, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41623205618569 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460356408519 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_25 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41605951804893 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301786043801 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨25, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41605951804893 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301786043801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_26 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (1299647191569 / 1562500000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150895023529 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨26, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (1299647191569 / 1562500000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150895023529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_27 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83142961156483 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (575448513961 / 25000000000000 : ℝ))
      (E := (cell12317 ⟨27, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83142961156483 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (575448513961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_28 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (10388565783201 / 12500000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301798014977 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨28, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (10388565783201 / 12500000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301798014977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_29 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41537057777789 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (287725255537 / 12500000000000 : ℝ))
      (E := (cell12317 ⟨29, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41537057777789 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (287725255537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_30 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41519864497173 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301806029703 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨30, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41519864497173 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301806029703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_31 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83005366550029 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (230181003217 / 10000000000000 : ℝ))
      (E := (cell12317 ⟨31, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83005366550029 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (230181003217 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_32 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82971028190907 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (230181399549 / 10000000000000 : ℝ))
      (E := (cell12317 ⟨32, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82971028190907 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (230181399549 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_33 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82936713885421 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (35965905941 / 1562500000000 : ℝ))
      (E := (cell12317 ⟨33, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82936713885421 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (35965905941 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_34 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41451211801087 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301821988227 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨34, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41451211801087 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301821988227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_35 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (8286815730993 / 10000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301826021127 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨35, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (8286815730993 / 10000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301826021127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_36 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82833914977611 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301829963097 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨36, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82833914977611 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301829963097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_37 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41399848287149 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460366798217 / 20000000000000 : ℝ))
      (E := (cell12317 ⟨37, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41399848287149 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460366798217 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_38 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (20691375517307 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (575459497197 / 25000000000000 : ℝ))
      (E := (cell12317 ⟨38, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (20691375517307 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (575459497197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_39 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (16546266286359 / 20000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150920978431 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨39, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (16546266286359 / 20000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150920978431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12318_20 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41692337860163 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301624213929 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨20, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41692337860163 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301624213929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_21 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (651172429519 / 781250000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301628203267 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨21, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (651172429519 / 781250000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301628203267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_22 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41657745322971 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150816089553 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨22, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41657745322971 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150816089553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_23 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (8328093468963 / 10000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150818102091 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨23, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (8328093468963 / 10000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150818102091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_24 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83246403076443 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (230164016609 / 10000000000000 : ℝ))
      (E := (cell12318 ⟨24, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83246403076443 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (230164016609 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_25 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83211895773499 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301644185419 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨25, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83211895773499 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301644185419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_26 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41588706374043 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301648149193 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨26, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41588706374043 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301648149193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_27 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (10392869245957 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575413044407 / 25000000000000 : ℝ))
      (E := (cell12318 ⟨27, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (10392869245957 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575413044407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_28 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41554259699917 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301656157183 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨28, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41554259699917 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301656157183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_29 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83074109012407 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150830074623 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨29, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83074109012407 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150830074623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_30 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83039722773329 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (460332831319 / 20000000000000 : ℝ))
      (E := (cell12318 ⟨30, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83039722773329 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (460332831319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_31 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83005360650717 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150834061639 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨31, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83005360650717 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150834061639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_32 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (20742755653213 / 25000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301672110059 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨32, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (20742755653213 / 25000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301672110059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_33 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (82936708628177 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301676119021 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨33, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (82936708628177 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301676119021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_34 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (16580483733059 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301680152021 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨34, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (16580483733059 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301680152021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_35 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (82868152692971 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (35963813961 / 1562500000000 : ℝ))
      (E := (cell12318 ⟨35, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (82868152692971 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (35963813961 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_36 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (1294279854377 / 1562500000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301688120573 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨36, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (1294279854377 / 1562500000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301688120573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_37 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (10349961574481 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575423029299 / 25000000000000 : ℝ))
      (E := (cell12318 ⟨37, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (10349961574481 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575423029299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_38 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (10345687301171 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301696084253 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨38, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (10345687301171 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301696084253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_39 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (82731328090083 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575425020271 / 25000000000000 : ℝ))
      (E := (cell12318 ⟨39, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (82731328090083 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575425020271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12319_20 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (16676933251847 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301482384783 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨20, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (16676933251847 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301482384783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_21 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (83350061843529 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (287685798653 / 12500000000000 : ℝ))
      (E := (cell12319 ⟨21, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (83350061843529 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (287685798653 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_22 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (8331548183677 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460298076189 / 20000000000000 : ℝ))
      (E := (cell12319 ⟨22, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (8331548183677 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460298076189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_23 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (16656185241147 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301494364371 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨23, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (16656185241147 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301494364371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_24 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (8324639491737 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (230149834369 / 10000000000000 : ℝ))
      (E := (cell12319 ⟨24, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (8324639491737 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (230149834369 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_25 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41605943969397 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301502381207 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨25, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41605943969397 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301502381207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_26 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (16635481047459 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460301272789 / 20000000000000 : ℝ))
      (E := (cell12319 ⟨26, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (16635481047459 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460301272789 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_27 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (8314294678033 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301510353713 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨27, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (8314294678033 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301510353713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_28 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (519428203347 / 625000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460302870751 / 20000000000000 : ℝ))
      (E := (cell12319 ⟨28, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (519428203347 / 625000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460302870751 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_29 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (16614820494131 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301518367079 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨29, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (16614820494131 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301518367079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_30 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (8303971655369 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460304467597 / 20000000000000 : ℝ))
      (E := (cell12319 ⟨30, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (8303971655369 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460304467597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_31 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (83005354752743 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150763163723 / 50000000000000 : ℝ))
      (E := (cell12319 ⟨31, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (83005354752743 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150763163723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_32 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (1296422141189 / 1562500000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301530337773 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨32, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (1296422141189 / 1562500000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301530337773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_33 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (82936703372191 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301534312509 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨33, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (82936703372191 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301534312509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_34 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (16580482745927 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301538312003 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨34, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (16580482745927 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301538312003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_35 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (82868148077191 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301542337883 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨35, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (82868148077191 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301542337883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_36 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (10354238297973 / 12500000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301546332933 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨36, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (10354238297973 / 12500000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301546332933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_37 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (16559937723699 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150775149129 / 50000000000000 : ℝ))
      (E := (cell12319 ⟨37, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (16559937723699 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150775149129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_38 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41382747375283 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460310858679 / 20000000000000 : ℝ))
      (E := (cell12319 ⟨38, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41382747375283 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460310858679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_39 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (8273132474939 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301558319069 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨39, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (8273132474939 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301558319069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12320_20 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (10423082099991 / 12500000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301340667723 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨20, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (10423082099991 / 12500000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301340667723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_21 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (8335005271037 / 10000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301344629093 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨21, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (8335005271037 / 10000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301344629093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_22 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (41657736514651 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (57533715919 / 2500000000000 : ℝ))
      (E := (cell12320 ⟨22, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (41657736514651 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (57533715919 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_23 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83280917723501 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (143834539807 / 6250000000000 : ℝ))
      (E := (cell12320 ⟨23, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83280917723501 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (143834539807 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_24 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83246386759917 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575339158433 / 25000000000000 : ℝ))
      (E := (cell12320 ⟨24, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83246386759917 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575339158433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_25 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83211880105669 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301360631169 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨25, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83211880105669 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301360631169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_26 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (16635479545609 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (460272926587 / 20000000000000 : ℝ))
      (E := (cell12320 ⟨26, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (16635479545609 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (460272926587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_27 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (41571469797251 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301368642507 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨27, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (41571469797251 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301368642507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_28 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (16621701134533 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (287671575587 / 12500000000000 : ℝ))
      (E := (cell12320 ⟨28, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (16621701134533 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (287671575587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_29 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (41537047965161 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (143836039959 / 6250000000000 : ℝ))
      (E := (cell12320 ⟨29, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (41537047965161 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (143836039959 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_30 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (8303971033543 / 10000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150690316173 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨30, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (8303971033543 / 10000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150690316173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_31 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83005348856107 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (35959134159 / 1562500000000 : ℝ))
      (E := (cell12320 ⟨31, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83005348856107 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (35959134159 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_32 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82971011460637 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301388620117 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨32, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82971011460637 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301388620117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_33 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82936698117463 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (460278523847 / 20000000000000 : ℝ))
      (E := (cell12320 ⟨33, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82936698117463 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (460278523847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_34 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82902408795191 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (71918643291 / 3125000000000 : ℝ))
      (E := (cell12320 ⟨34, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82902408795191 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (71918643291 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_35 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82868143462587 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150700289247 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨35, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82868143462587 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150700289247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_36 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (647139860067 / 781250000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150702300091 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨36, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (647139860067 / 781250000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150702300091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_37 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82799684642241 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575352148227 / 25000000000000 : ℝ))
      (E := (cell12320 ⟨37, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82799684642241 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575352148227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_38 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (41382745546411 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301412557551 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨38, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (41382745546411 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301412557551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_39 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (16546264281943 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301416553449 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨39, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (16546264281943 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301416553449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12321_20 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20846161835601 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301199004513 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨20, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20846161835601 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301199004513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_21 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (83350043578953 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301202981139 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨21, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (83350043578953 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301202981139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_22 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (16663092844707 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301207004843 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨22, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (16663092844707 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301207004843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_23 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (83280909242929 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150605481749 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨23, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (83280909242929 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150605481749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_24 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (16649275720817 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575303744471 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨24, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (16649275720817 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575303744471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_25 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20802968068531 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301218993663 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨25, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20802968068531 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301218993663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_26 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41588695110167 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301222956167 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨26, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41588695110167 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301222956167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_27 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41571466205087 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (460245397121 / 20000000000000 : ℝ))
      (E := (cell12321 ⟨27, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41571466205087 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (460245397121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_28 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20777124702817 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575307742109 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨28, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20777124702817 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575307742109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_29 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (83074089391407 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150617483023 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨29, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (83074089391407 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150617483023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_30 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (83039704118547 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301238981209 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨30, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (83039704118547 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301238981209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_31 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (83005342960809 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230124295797 / 10000000000000 : ℝ))
      (E := (cell12321 ⟨31, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (83005342960809 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230124295797 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_32 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20742751471619 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575311739273 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨32, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20742751471619 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575311739273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_33 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (10367086607999 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (17978522829 / 781250000000 : ℝ))
      (E := (cell12321 ⟨33, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (10367086607999 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (17978522829 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_34 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (16580480772393 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (115062745669 / 5000000000000 : ℝ))
      (E := (cell12321 ⟨34, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (16580480772393 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (115062745669 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_35 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41434069424581 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (57531473313 / 2500000000000 : ℝ))
      (E := (cell12321 ⟨35, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41434069424581 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (57531473313 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_36 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (82833897794507 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150631461159 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨36, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (82833897794507 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150631461159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_37 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20699920166771 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301266942513 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨37, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20699920166771 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301266942513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_38 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (10345685929517 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575317733847 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨38, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (10345685929517 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575317733847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_39 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41365659035529 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301274901597 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨39, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41365659035529 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301274901597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12322_20 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (10423079735833 / 12500000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301057395151 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨20, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (10423079735833 / 12500000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301057395151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_21 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41675017224639 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301061387101 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨21, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41675017224639 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301061387101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_22 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (83315455419469 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150532713453 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨22, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (83315455419469 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150532713453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_23 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41640450382009 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150534701219 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨23, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41640450382009 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150534701219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_24 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41623185224937 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301073376147 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨24, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41623185224937 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301073376147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_25 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41605932222079 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460215482067 / 20000000000000 : ℝ))
      (E := (cell12322 ⟨25, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41605932222079 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460215482067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_26 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41588691357081 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (115054069601 / 5000000000000 : ℝ))
      (E := (cell12322 ⟨26, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41588691357081 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (115054069601 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_27 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (5196432826709 / 6250000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230108538301 / 10000000000000 : ℝ))
      (E := (cell12322 ⟨27, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (5196432826709 / 6250000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230108538301 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_28 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (83108491951329 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301089386547 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨28, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (83108491951329 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301089386547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_29 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (8307408285391 / 10000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301093347183 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨29, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (8307408285391 / 10000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301093347183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_30 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41519848951521 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301097384573 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨30, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41519848951521 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301097384573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_31 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (2593916783339 / 3125000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230110138433 / 10000000000000 : ℝ))
      (E := (cell12322 ⟨31, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (2593916783339 / 3125000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230110138433 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_32 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (20742750078403 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301105348697 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨32, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (20742750078403 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301105348697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_33 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82936687611779 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301109338227 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨33, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82936687611779 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301109338227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_34 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (20725599732489 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (287639169347 / 12500000000000 : ℝ))
      (E := (cell12322 ⟨34, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (20725599732489 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (287639169347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_35 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82868134236913 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575279335343 / 25000000000000 : ℝ))
      (E := (cell12322 ⟨35, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82868134236913 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575279335343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_36 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41416946750787 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301121357959 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨36, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41416946750787 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301121357959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_37 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (3311987067721 / 4000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230112534707 / 10000000000000 : ℝ))
      (E := (cell12322 ⟨37, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (3311987067721 / 4000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230112534707 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_38 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82765483780507 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301129309581 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨38, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82765483780507 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301129309581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_39 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82731314733419 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301133304827 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨39, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82731314733419 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301133304827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12323_20 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41692314216353 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300915897881 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨20, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41692314216353 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300915897881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_21 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (16670005064269 / 20000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300919905243 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨21, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (16670005064269 / 20000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300919905243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_22 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (16663089323421 / 20000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300923902951 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨22, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (16663089323421 / 20000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300923902951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_23 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83280892286767 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575231973857 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨23, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83280892286767 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575231973857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_24 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41623181148641 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300931886857 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨24, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41623181148641 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300931886857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_25 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (20802964153943 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (71904246287 / 3125000000000 : ℝ))
      (E := (cell12323 ⟨25, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (20802964153943 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (71904246287 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_26 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83177375209529 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575234970529 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨26, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83177375209529 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575234970529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_27 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (20785729511503 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300943893129 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨27, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (20785729511503 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300943893129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_28 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (5194280318303 / 6250000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (287618482379 / 12500000000000 : ℝ))
      (E := (cell12323 ⟨28, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (5194280318303 / 6250000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (287618482379 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_29 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (8307407631783 / 10000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300951841211 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨29, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (8307407631783 / 10000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300951841211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_30 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41519845844457 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300955842441 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨30, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41519845844457 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300955842441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_31 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (5187833198389 / 6250000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300959865259 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨31, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (5187833198389 / 6250000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300959865259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_32 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (20742748685511 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300963853457 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨32, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (20742748685511 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300963853457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_33 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82936682360821 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575241966897 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨33, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82936682360821 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575241966897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_34 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (20725598499791 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150485925467 / 50000000000000 : ℝ))
      (E := (cell12323 ⟨34, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (20725598499791 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150485925467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_35 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (1035851620323 / 1250000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300975863643 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨35, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (1035851620323 / 1250000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300975863643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_36 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41416944604889 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575244962123 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨36, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41416944604889 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575244962123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_37 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41399836360031 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (460196761317 / 20000000000000 : ℝ))
      (E := (cell12323 ⟨37, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41399836360031 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (460196761317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_38 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (16553096025187 / 20000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300987797457 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨38, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (16553096025187 / 20000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300987797457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_39 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82731311396797 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575247955457 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨39, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82731311396797 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575247955457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12324_20 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83384618980531 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (35949600851 / 1562500000000 : ℝ))
      (E := (cell12324 ⟨20, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83384618980531 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (35949600851 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_21 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83350016195153 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300778477303 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨21, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83350016195153 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300778477303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_22 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83315437816441 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300782432981 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨22, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83315437816441 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300782432981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_23 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (10410110476397 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300786442467 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨23, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (10410110476397 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300786442467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_24 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83246354146309 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150395225841 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨24, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83246354146309 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150395225841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_25 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (16642369757793 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300794464569 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨25, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (16642369757793 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300794464569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_26 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41588683853217 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150399213229 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨26, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41588683853217 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150399213229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_27 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41571455433089 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575200614389 / 25000000000000 : ℝ))
      (E := (cell12324 ⟨27, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41571455433089 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575200614389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_28 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (3324339129433 / 4000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150403222159 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨28, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (3324339129433 / 4000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150403222159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_29 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83074069783167 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300810448129 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨29, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83074069783167 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300810448129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_30 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83039685476163 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300814413287 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨30, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83039685476163 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300814413287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_31 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83005325282937 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300818400757 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨31, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83005325282937 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300818400757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_32 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82970989171773 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (46016448257 / 2000000000000 : ℝ))
      (E := (cell12324 ⟨32, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82970989171773 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (46016448257 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_33 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82936677111121 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (23008263931 / 1000000000000 : ℝ))
      (E := (cell12324 ⟨33, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82936677111121 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (23008263931 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_34 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (20725597267397 / 25000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (35950475029 / 1562500000000 : ℝ))
      (E := (cell12324 ⟨34, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (20725597267397 / 25000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (35950475029 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_35 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (10358515626993 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300834382149 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨35, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (10358515626993 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300834382149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_36 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41416942459559 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150419196959 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨36, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41416942459559 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150419196959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_37 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (16559933749639 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460168475939 / 20000000000000 : ℝ))
      (E := (cell12324 ⟨37, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (16559933749639 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460168475939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_38 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (4138273823621 / 5000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (287605799877 / 12500000000000 : ℝ))
      (E := (cell12324 ⟨38, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (4138273823621 / 5000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (287605799877 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_39 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (10341413507649 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150425196957 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨39, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (10341413507649 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150425196957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

end BstLean.Part263
